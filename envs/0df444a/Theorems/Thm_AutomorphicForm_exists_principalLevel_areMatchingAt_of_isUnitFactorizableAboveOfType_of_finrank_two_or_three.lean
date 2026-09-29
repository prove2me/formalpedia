-- Prove2me | Theorems.Thm_AutomorphicForm_exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three
-- name    : AutomorphicForm.exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/debf3241-27a3-59fc-904a-435c00c43597
-- title:
--   Matching test functions for cyclic base change in degree 2 or 3
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ of degree $2$ or $3$, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, let $S_K$ be a finite set of height-one primes of $\mathcal{O}_K$, let $N$ be an ideal of $\mathcal{O}_L$, let $\mathrm{tys}_L$ be an archimedean type family for $L$ (for each infinite place $w$ of $L$ a finite list of representations of the isometry subgroup of $L_w$), and let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ satisfy `IsUnitFactorizableAboveOfType` for the subgroup $U$ of elements of `levelOne` at $N$ with trivial archimedean component: that is, $\varphi$ is bi-invariant under $U$, is $\mathrm{tys}_L$-bi-finite at the archimedean places, and admits a semi-local factorisation — an archimedean test factor $\varphi_a$, a finite test factor $\varphi_f$ and semi-local test functions $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for $v \in S_K$, with $\varphi_f$ equal to $\prod_{v \in S_K} \varphi_{S,v}$ of the semi-local components at points integral above every prime outside $S_K$, zero at points failing integrality above some such prime, and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_{\mathrm{fin}})$. Then there exist a nonzero ideal $N'$ of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, an archimedean type family $\mathrm{tys}_K$ for $K$, and a continuous, compactly supported $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which is unit-factorizable of type $\mathrm{tys}_K$ at $S_K$ for the subgroup of elements of `principalLevel` at $N'$ with trivial archimedean component, and which matches $\varphi$ in the sense of `AreMatchingAt`: factorisations of $\varphi$ and $f$ as above exist whose archimedean factors satisfy the $\sigma$-twisted archimedean matching relation and whose factors at each $v \in S_K$ satisfy the $\sigma$-twisted local matching relation.
--
--   This is the existence of matching test functions for cyclic base change on $\mathrm{GL}(2)$ in degree $2$ or $3$, with the function on the base field produced at a principal congruence level supported in $S_K$ rather than at the level of the given function upstairs. It feeds the comparison of twisted and ordinary trace contributions, being cited by [`AutomorphicForm.exists_mem_cuspClasses_of_twistedCutTrace_ne_zero_of_finrank_two_or_three`](thm.html#AutomorphicForm.exists_mem_cuspClasses_of_twistedCutTrace_ne_zero_of_finrank_two_or_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain

theorem AutomorphicForm.exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ) :
    ∃ (N' : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ),
      N' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK) ∧
      Continuous f ∧ HasCompactSupport f ∧
      IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f ∧
      AreMatchingAt K L σ SK φ f := by sorry
