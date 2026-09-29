-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
-- name    : AutomorphicForm.whittakerCoefficient_unipotentGL2_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/7f9dedbd-4ac7-5e04-b987-657e73cfca95
-- title:
--   Unipotent covariance of adelic Whittaker coefficients on GL₂
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the adelic general linear group. Fix arbitrary data $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_F$, and a family $\mathrm{gen}$ of elements indexed by the height-one spectrum of $\mathcal{O}_F$; these are assembled into the record `productionPinsOf F D U gen (adelicBox F)`, whose measure on $\mathbb{A}_F$ is the additive Haar measure `adelicAddHaar` conditioned on the adelic box $\{x : x_\infty \in$ the fundamental domain of the lattice basis of the mixed space, $x_{\mathrm{fin}}$ integral at every finite place$\}$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on the image of $F$ (the predicate `IsPrincipalInvariantAddChar`), let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, let $g \in \mathrm{GL}_2(\mathbb{A}_F)$, and assume the slice $u \mapsto \varphi(n(u)g)$ is $F$-periodic, i.e. $\varphi(n(\beta + u)g) = \varphi(n(u)g)$ for all $\beta \in F$ and $u \in \mathbb{A}_F$, where $n(u) = \begin{pmatrix}1 & u \\ 0 & 1\end{pmatrix}$ is `unipotentGL2`. Then for every $\alpha \in F$ and every $x \in \mathbb{A}_F$, the Whittaker coefficient $W_\alpha(h) = \int \varphi(n(u)h)\,\psi(-(\alpha u))\,d\nu(u)$ satisfies $W_\alpha(n(x)g) = \psi(\alpha x)\,W_\alpha(g)$.
--
--   This is the covariance of Fourier–Whittaker coefficients on $\mathrm{GL}_2$ under the adelic unipotent radical: the $\alpha$-th coefficient transforms by the character $n(x) \mapsto \psi(\alpha x)$, the periodicity hypothesis being automatic for functions invariant under $\mathrm{GL}_2(F)$ on the left. It is used throughout the development of adelic automorphic forms, for instance in the analysis of cuspidal constituents and in bounds on class sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul.lean

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem AutomorphicForm.whittakerCoefficient_unipotentGL2_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (α : F) (x : AdeleRing (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α (unipotentGL2 x * g) =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g := by sorry
