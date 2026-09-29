-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot
-- name    : AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/b7a1d20d-a789-5c76-8e4d-b559752d0c6d
-- title:
--   Pure rotation character in a non-zero level-and-type cut
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}D_0x$ for the union of the right translates by $x\in T$ of the centre-cut Siegel set $D_0$ consisting of those $g$ whose finite part lies in the integral subset `finiteIntegralGL2`, whose archimedean component at each infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, i.e. for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and a unit $z$ of $\mathbb{A}_K$ with $\gamma g\,z\in D$. Let `pins` be the production carrier data on $D$ with level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\text{archimedean projection})$, Hecke generators `heckeGen` at the finite places, and the adelic box as conditioning set; its central subgroup is all of $\mathbb{A}_K^\times$, so $\xi$ is a character of that group. Let $V\subseteq(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ be a $\mathbb{C}$-submodule which is a cuspidal constituent for `pins` and $\xi$: a non-zero cusp subrepresentation all of whose cusp subrepresentations contained in it are $\bot$ or $V$. Assume every infinite place of $K$ is real, let $N\neq 0$ be an ideal of $\mathcal{O}_K$ and `tys` an archimedean type family (a finite family of archimedean representation types at each infinite place) such that the cut $V\cap\{\varphi:\varphi(gu)=\varphi(g)\ \forall u\in \mathrm{levelOne}(N)\cap\ker(\text{arch.\ projection})\}\cap \mathrm{archCut}(\mathrm{tys})$ is non-zero. Then there is a family $\chi=(\chi_v)_v$ of characters $\chi_v:\mathrm{rowIsometrySubgroup}_0(K_v)\to\mathbb{C}^\times$, one at each infinite place, such that the same intersection with $\mathrm{archCut}(\mathrm{tys})$ replaced by the cut for the one-character-per-place family $\mathrm{ofChar}(\chi)$ is still non-zero.
--
--   This is the passage from a general archimedean $K$-type cut to a cut by a single character of the rotation group at each real place: over a totally real field, a non-zero vector of the level-$N$ type cut of a cuspidal constituent can be replaced by a non-zero vector of pure rotation weight at every infinite place. It is used in establishing archimedean smoothness and the Casimir eigenvalue property for cuspidal constituents over totally real fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥) :
    ∃ χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ,
      V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ) ≠ ⊥ := by sorry
