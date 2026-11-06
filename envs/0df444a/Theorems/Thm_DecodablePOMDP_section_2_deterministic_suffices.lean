-- Prove2me | Theorems.Thm_DecodablePOMDP_section_2_deterministic_suffices
-- name    : DecodablePOMDP.section_2_deterministic_suffices
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:56.18559+00:00
-- url     : https://prove2.me/theorems/cfa45232-290a-432c-aa8f-7b3cc5f78571
-- title:
--   §2, p.6 — randomised and deterministic policies have the same optimal value, attained
-- statement:
--   Let $\mathcal P$ be a valid POMDP with a nonempty action set. Then the optimal value over all history-dependent randomised policies is attained by a deterministic policy, and no deterministic policy exceeds it:
--
--   $$\exists\,\sigma\text{ deterministic}:\ V^\sigma_{\mathcal P}=V^*_{\mathcal P},\qquad V^\sigma_{\mathcal P}\le V^*_{\mathcal P}\ \text{ for every deterministic }\sigma.$$
--
--   Hence $V^*_{\mathcal P}$ is a maximum over deterministic policies. Theorem 1 measures its output against this optimal value, and Lemma 1's proof uses the equality of the two optimal values.
--
--   Differences from the source:
--   - encoding: "the optimal value of the POMDP with randomised policies is the same as that with deterministic policies" and "the supremum is attainable" → some deterministic σ has V^σ = V* (sup over randomised), and every deterministic σ has V^σ ≤ V*; reason: the two clauses say exactly that V* is a maximum over deterministic policies, which is the printed equality with attainment
--   - encoding: a randomised policy is a mixture of deterministic policies (private seed) → behavioural randomised policies (a probability vector of actions per history); reason: every seed mixture has a behavioural policy with the same law of trajectories, and conversely; the values coincide
--   - encoding: action space of size A (implicitly A ≥ 1) → `[Nonempty A]`; reason: with no action there is no policy; the paper's A ≥ 1
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §2, p.6

import Mathlib
import Definitions.Def_DecodablePOMDP_Value

namespace DecodablePOMDP

/-- **§2, p.6 — randomised and deterministic policies have the same optimal value, and it is
attained.** For every valid POMDP with a nonempty action set, some deterministic history policy
`σ` has `V^σ_P = V*_P` (the supremum over history-dependent randomised policies), and every
deterministic policy has value at most `V*_P`; so `V*_P` is a maximum over deterministic policies.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, p.6: "Since the state, action,
observation alphabets and the horizon-length are finite, the supremum is attainable, i.e., there
exists an optimal policy π∗ such that V∗P = V^{π∗}_P. … Fixing the seed yields a deterministic
policy, and thus a randomised policy is a mixture of deterministic policies. From this, it readily
follows that optimal value of the POMDP with randomised policies is the same as that with
deterministic policies." -/
theorem section_2_deterministic_suffices {S A O : Type} [Fintype S] [Fintype A] [Fintype O]
    [DecidableEq A] [Nonempty A] (P : POMDP S A O) (hP : P.IsValid) :
    (∃ σ : DetPolicyFn A O, value P (toRand σ) = optValue P) ∧
    ∀ σ : DetPolicyFn A O, value P (toRand σ) ≤ optValue P := by sorry

end DecodablePOMDP
