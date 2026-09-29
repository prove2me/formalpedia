-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a1445e5f-a57a-58c1-8cd2-f264a108762b
-- title:
--   Whittaker coefficients of cut cusp vectors are bounded
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $D=\bigcup_{x\in T}(\,\cdot\,x)\bigl(\text{centreCutSiegelSet}\bigr)$ of right translates of the centre-cut Siegel set (those $g$ whose finite part is integral, whose archimedean component at each infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$) satisfies `CoversModCentre`: every $g$ can be moved into $D$ by a global matrix on the left and an adelic central scalar on the right. Consider the carrier data `productionPinsOf` with domain $D$, level groups $N\mapsto \text{levelOne}(N)\cap\ker(\text{glArch})$, Hecke generators $\text{heckeGen}$ at the finite places, and conditioning set the adelic box, so that the central subgroup is all of $\mathbb{A}_K^\times$ and the unipotent measure is the adelic additive Haar measure conditioned on the box. Let $\xi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a character with $\lVert\xi(z)\rVert=\lVert z\rVert_{\mathbb{A}}^{w_0}$ for all $z$, where $w_0\in\mathbb{R}$ and $\lVert\cdot\rVert_{\mathbb{A}}$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19). Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $\mathrm{tys}$ be an `ArchTypeFamily` (a number $\mathrm{card}(w)$ of archimedean types at each infinite place together with those types), and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data and $\xi$, i.e. $V$ satisfies the predicate `IsCuspSubrep`, is nonzero, and every `IsCuspSubrep` submodule contained in $V$ is $0$ or $V$. Let $y$ lie in $V$, be right invariant under $\text{levelOne}(N)\cap\ker(\text{glArch})$, and lie in the archimedean cut submodule, namely at every infinite place $w$ in the sum of the submodules `archTypeSubmoduleAt` attached to the types $\mathrm{tys}.\mathrm{rep}\,w\,i$. Then there exists $M\in\mathbb{R}$ such that for every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ the first Whittaker coefficient of $y$ for the standard additive character, $\int y(n(x)g)\,\psi_K(-x)\,d\nu(x)$ with $n(x)$ the upper unipotent matrix and $\nu$ the conditioned measure, has norm at most $M\,\lVert\det g\rVert_{\mathbb{A}}^{w_0/2}$.
--
--   This is the moderate-growth bound for the first Fourier–Whittaker coefficient of a level- and type-cut vector in a cuspidal constituent of $\mathrm{GL}_2$ over a number field: the same determinant-power bound that holds for the cusp form itself persists after integration along the unipotent. It feeds the verification of the core hypotheses attached to vectors in the cut space, including the archimedean character and highest-weight analyses at real and complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_norm_whittakerCoefficient_le_mul_ideleNorm_det_rpow_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 g‖ ≤
        M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) := by sorry
