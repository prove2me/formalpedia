-- Prove2me | Theorems.Thm_EfronBroadcast_Main_byzantine_broadcast
-- name    : EfronBroadcast.Main.byzantine_broadcast
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:50.062639+00:00
-- url     : https://prove2.me/theorems/31d4c757-4cb0-4cf5-900f-d75ae792f041
-- title:
--   Theorem 1 — deterministic Byzantine broadcast with near-quadratic communication
-- statement:
--   For every constant $\kappa$ bounding the primitive sizes there is a constant $C$ with the following property. For all $n>0$ and $t<n$ there are public comparison graphs such that, for every leader $\ell$, input bit $b$, security parameter $\lambda>\log_2 n$, primitive sizes bounded by $\kappa$, and $t$-bounded adversary with ideal signatures, the deterministic Protocol 1 (with its Dolev–Strong branch when $t<E$) satisfies termination, agreement and validity, and runs for at most $6t+1$ rounds, and for $n\ge2$ the bits sent by correct parties are at most
--   $$
--   C\,n^2\log_2^4(n)\,\lambda.
--   $$
--
--   Differences from the source:
--   - generalization: there exists a t-secure deterministic BB protocol → this specific local-rule protocol, Protocol 1, is t-secure with the bounds; reason: the specific witness is the one of the source proof, and its security implies existence; a bare existential over all functions of the state would be unsound for symbolic primitives
--   - generalization: n a power of two by the standing assumption of §2, with the remark that the results generalize to arbitrary n → every positive n, with the value indices padded to 2^⌈log₂ n⌉ and exactly n physical parties; reason: at n = 2^k this is the source protocol, and physical parties are not padded, so the O(t) rounds are kept
--   - generalization: O(t) rounds → the round count is at most 6t + 1 for every t, including t = 0; reason: 6t + 1 ≤ 7t for t ≥ 1, and this is the bound of Claim 7 and of the Dolev–Strong branch; at t = 0 a literal bound C·0 is impossible with n ≥ 2 and the source intends the asymptotic reading
--   - encoding: O(n² log⁴(n) λ) with primitive sizes O(λ) and O(λ log L) → for each κ, one C before n, t, the graphs, leader, input, λ, primitive sizes and adversary, and the bit bound at n ≥ 2; reason: the source estimates are uniform, and the source bound is 0 at n = 1, where it is meaningful only asymptotically
--   - encoding: adversary controlling corrupt parties in a synchronous network, signatures that cannot be forged, a binding vector commitment, a PKI → all corruption-time maps and message tables of NetAdversary subject to Unforgeable, signer identities in symbolic signatures, and the commitment represented by the committed list itself and charged the commitment length; reason: a deterministic protocol has one run per adversary, so this covers every adaptive strategy; correct parties use the list only through opening verification
--   - encoding: the graphs of Lemma 2, for c in {1, …, n} → graphs with the same property for c up to 2^⌈log₂ n⌉ on n vertices; reason: for c > n the property forces a complete graph between nonempty disjoint sets; at n = 2^k the ranges agree
--   - reading: Dolev–Strong accepts in rounds r ≤ t + 1 and multicasts all r + 1 signatures, and takes t + 1 rounds → messages are sent in rounds 0, …, t, with r + 1 signatures chosen among those held, and the acceptance of round t + 1 is local; reason: this is the timing that gives the t + 1 rounds and O(n²(t + 1)λ) bits of the proof of Theorem 1
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 2, PDF p. 3, Theorem 1; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
import Definitions.Def_EfronBroadcast_Main_Broadcast
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Theorem 1, p. 2 (PDF p. 3). `κ` bounds the primitive sizes; `C` is chosen before `n, t` and the
graphs, which are public and fixed before the leader, input, primitive sizes and execution. The
witness is Protocol 1, with its Dolev--Strong branch; all three properties of Definition 1 hold in
`BBSpec`. The bit bound is stated for `n ≥ 2`, since the source's `log⁴ n` vanishes at `n = 1`. -/
theorem byzantine_broadcast :
    ∀ κ : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ n t : ℕ, 0 < n → t < n →
      ∃ G : ℕ → SimpleGraph (Party n), ComparisonFamily C (Nat.clog 2 n) G ∧
      ∀ (ℓ : Party n) (input : Bool) (lam : ℕ), Real.logb 2 n < lam →
      ∀ (Z : PrimitiveSizes), Z.Bounded κ lam →
      let cfg : BBConfig n (Nat.clog 2 n) := ⟨Nat.le_pow_clog (by norm_num) n, G, ℓ, t⟩
      ∀ adv : NetAdversary n (BBMsg n (Nat.clog 2 n)), BBAdmissible cfg input adv →
      BBSpec (bbMachine cfg input) BBState.decision ℓ input adv (bbRounds (Nat.clog 2 n) t) ∧
      bbRounds (Nat.clog 2 n) t ≤ 6 * t + 1 ∧
      (2 ≤ n →
        (correctBits (bbMachine cfg input) adv (bbMsgBits Z) (bbRounds (Nat.clog 2 n) t) : ℝ) ≤
          C * (n : ℝ) ^ 2 * (Real.logb 2 n) ^ 4 * lam) := by sorry

end EfronBroadcast.Main
