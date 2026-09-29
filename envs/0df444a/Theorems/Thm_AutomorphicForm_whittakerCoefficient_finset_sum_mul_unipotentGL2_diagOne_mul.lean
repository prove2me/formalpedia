-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
-- name    : AutomorphicForm.whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/11c2a735-4f60-5695-9f53-d4d8ed08e106
-- title:
--   Whittaker coefficients of unipotent right translates at torus points
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F$ and $\mathrm{GL}_2(\mathbb{A}_F)$ written as `AdelicGL2 (𝓞 F) F`. Fix data $D$ (a subset of $\mathrm{GL}_2(\mathbb{A}_F)$), $U$ (a family of subgroups indexed by ideals of $\mathcal{O}_F$) and `gen` (a choice of element for each finite place), assembled into `productionPinsOf F D U gen (adelicBox F)`; the Whittaker integral below uses from this record only the Borel structure on $\mathbb{A}_F$ and the measure $\nu$, namely the adelic additive Haar measure conditioned on the standard box $\mathbb{A}_F$-box `adelicBox F` (infinite part in a fundamental domain for the lattice, finite part integral). Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on the image of $F$ (hypothesis `hψ`), and let $G : \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy $G(n(\beta+u)h)=G(n(u)h)$ for all $\beta\in F$, $u\in\mathbb{A}_F$ and $h\in\mathrm{GL}_2(\mathbb{A}_F)$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Here $W_\alpha(\varphi)(h)=\int_{\mathbb{A}_F}\varphi(n(x)h)\,\psi(-\alpha x)\,d\nu(x)$ for $\alpha\in F$. Let $\iota$ be a finite set of adeles, $c:\mathbb{A}_F\to\mathbb{C}$ a coefficient function, $\alpha\in F$, $a$ an idele, $g\in\mathrm{GL}_2(\mathbb{A}_F)$, and write $t=\mathrm{diag}(a,1)\,g$. Assume $g$ commutes with $n(y)$ for every $y\in\iota$, and that for each $y\in\iota$ the function $x\mapsto G(n(x)\,t\,n(y))\,\psi(-(\alpha x))$ is $\nu$-integrable. Then $$W_\alpha\Bigl(\sum_{y\in\iota}c_y\,G(\,\cdot\,n(y))\Bigr)(t)=\Bigl(\sum_{y\in\iota}c_y\,\psi(\alpha\,a\,y)\Bigr)\cdot W_\alpha(G)(t).$$
--
--   This is the standard covariance of Whittaker coefficients under right translation by unipotent elements, evaluated along the diagonal torus: a finite combination of right unipotent translates of $G$ has Whittaker coefficient equal to that of $G$ times a trigonometric polynomial $\sum_y c_y\psi(\alpha a y)$ in $a$. It is used in the existence results [`AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul`](thm.html#AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul) and its ball and shell variants, where the multiplier is engineered to approximate a prescribed function of the idele $a$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul.lean

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicLevel

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem AutomorphicForm.whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F),
      G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * h) = G (unipotentGL2 u * h))
    (ι : Finset (AdeleRing (𝓞 F) F)) (c : AdeleRing (𝓞 F) F → ℂ)
    (α : F) (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F)
    (hcomm : ∀ y ∈ ι, g * unipotentGL2 y = unipotentGL2 y * g)
    (hint : ∀ y ∈ ι, WhittakerCoefficientIntegrable F (productionPinsOf F D U gen (adelicBox F)) ψ
      (fun x => G (x * unipotentGL2 y)) α (diagOne a * g)) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ
        (fun x => ∑ y ∈ ι, c y * G (x * unipotentGL2 y)) α (diagOne a * g) =
      (∑ y ∈ ι, c y * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * ((a : AdeleRing (𝓞 F) F) * y))) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ G α (diagOne a * g) := by sorry
