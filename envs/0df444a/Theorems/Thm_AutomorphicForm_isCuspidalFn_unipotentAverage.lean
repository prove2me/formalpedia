-- Prove2me | Theorems.Thm_AutomorphicForm_isCuspidalFn_unipotentAverage
-- name    : AutomorphicForm.isCuspidalFn_unipotentAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/03d8be4d-a927-51b2-99d3-8b83a4832238
-- title:
--   Schwartz–Bruhat unipotent averages of cuspidal functions are cuspidal
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the general linear group of degree $2$ over the adele ring of $F$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ for `unipotentGL2`. Fix carrier data: a set $D\subseteq\mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups indexed by the ideals of $\mathcal{O}_F$, and a map $\mathrm{gen}$ from the height-one spectrum of $\mathcal{O}_F$ to $\mathrm{GL}_2(\mathbb{A}_F)$; through `productionPinsOf F D U gen (adelicBox F)` these determine on $\mathbb{A}_F$ the Borel $\sigma$-algebra and the measure $\nu$ obtained by conditioning the adelic additive Haar measure on the adelic box (infinite part in the fundamental domain of the lattice basis, finite part integral at every place), a measure that in fact does not involve $D$, $U$ or $\mathrm{gen}$. Let $G\colon\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and of moderate growth in the determinant: there are $C\in\mathbb{R}$ and $M\in\mathbb{N}$ with $\|G(g)\|\le C\max\bigl(\|\det g\|,\|\det g\|^{-1}\bigr)^{M}$ for all $g$, where $\|\cdot\|$ is the idele norm given by the module of the Haar character. Assume $G$ is cuspidal for these data, i.e. $\int G(n(q)g)\,d\nu(q)=0$ for every $g$. Let $B$ lie in the Schwartz–Bruhat space of $\mathbb{A}_F$ (the $\mathbb{C}$-span of pure tensors of a Schwartz function on the mixed space with a locally constant compactly supported function on the finite adeles), and let $\Phi$ satisfy $\Phi(h)=\int_{\mathbb{A}_F}B(x)\,G(h\,n(x))\,dx$ for all $h$, the integral being against the full adelic additive Haar measure. Then $\Phi$ is cuspidal for the same data: $\int \Phi(n(q)g)\,d\nu(q)=0$ for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the stability of cuspidality under right convolution along the unipotent radical by a Schwartz–Bruhat function, as used in the construction of Whittaker expansions for automorphic forms on $\mathrm{GL}_2$ over a number field. It feeds the summation formula for the Whittaker coefficient at the identity over principal ideles, [`AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage`](thm.html#AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCuspidalFn_unipotentAverage.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

theorem AutomorphicForm.isCuspidalFn_unipotentAverage
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 G)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) :
    @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 Φ := by sorry
