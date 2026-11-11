-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_prop3_wide_replacement
-- name    : ExpanderWalkDecode.Main.prop3_wide_replacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:22:28.382069+00:00
-- url     : https://prove2.me/theorems/17d4d605-c875-4205-b27d-749247312e04
-- title:
--   Proposition 3 (Restated) — explicit compatible graphs, walk count and operator amplification
-- statement:
--   Let $s\ge1$ with $4\mid s$ and $\lambda=(s^2-1)2^{-s/4}\le1/4$. Then there are outer graphs $A_n$ ($n\in\mathbb N$) with ports $\mathbb F_2^s$ and one inner Cayley graph $B$ on $(\mathbb F_2^s)^s=\mathbb F_2^{s^2}$ with $2^{s/2}$ distinct generators such that:
--
--   1. $|A_n|=n(1+o_n(1))$, with $n\le|A_n|$ for all large $n$;
--   2. every $A_n$ is locally invertible with expansion at most $\lambda^2$, and $B$ has expansion at most $\lambda$;
--   3. for all $n$ and $t$, $|\mathrm{WRW}^t_s|\le|A_n|\cdot2^{s(s+t/2)}$;
--   4. for all $n,t,D$ and every family $\{U_a\}_{a\in A_n}$ of symmetric orthogonal $D\times D$ matrices,
--   $$\big\|\mathbb E_{\vec a\sim\mathrm{WRW}^t_s}[U_{a_0}\cdots U_{a_t}]\big\|_{\mathrm{op}}^2\ge2\Big(\frac1{9\lambda^4}\Big)^{1+t/s}(19\lambda^2)^t\ \Longrightarrow\ \big\|\mathbb E_a[U_a]\big\|_{\mathrm{op}}\ge4\lambda .$$
--
--   This packages the code construction: the walks give the code coordinates, item 3 is the size used in the rate calculation, and item 4 is the amplification used both for the bias of the code and for the decoder.
--
--   Differences from the source:
--   - reading: |A| = n·(1 + o_n(1)) → a family n ↦ A_n with n ≤ |A_n| ≤ (1+η)n for all n ≥ n₀(η); reason: the construction embeds [n] into A (§4, step 1), so |A| ≥ n
--   - reading: an outer graph A and a compatible inner graph B → A_n locally invertible with ports F_2^s (degree 2^s); B Cayley on (F_2^s)^s with 2^{s/2} distinct generators; reason: Definition 5 requires d = 2^m with |B| = 2^{ms}; the proof takes m = s, Proposition 4 (locally invertible) and Proposition 5 with r = s², ℓ = s/4; the generator enumeration is injective, respecting the Cayley subset definition on printed p. 21
--   - encoding: |WRW^t_s| ≤ n(1+o_n(1))·2^{s(s+t/2)} → card of the set of walks ≤ |A_n|·2^{s(s+t/2)}; reason: |A_n| is the n(1+o_n(1)) factor
--   - encoding: n, s ∈ ℕ with 4 | s → additionally 0 < s; reason: at s = 0 the exponent t/s is undefined
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 23 (PDF p. 26), Appendix B.3, Proposition 3 (Restated); first statement p. 10 (PDF p. 13)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_WideWalk

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Proposition 3 (Restated) (Appendix B.3, p. 23): for `4 ∣ s` with
`λ = (s² - 1) 2^{-s/4} ≤ 1/4` there are outer graphs `A_n` (ports `F₂^s`, `|A_n| = n (1 + o_n(1))`,
locally invertible, expansion `≤ λ²`) and one compatible inner Cayley graph `B` on `F₂^{s·s}` of
degree `2^{s/2}` and expansion `≤ λ`, with `|WRW^t_s| ≤ |A_n| 2^{s(s+t/2)}` for every `t`, and with
the operator amplification property for every `t`, every dimension and every family of
symmetric orthogonal matrices. -/
theorem prop3_wide_replacement (s : ℕ) (hs4 : 4 ∣ s) (hs : 0 < s)
    (hlam : ((s : ℝ) ^ 2 - 1) * (2 : ℝ) ^ (-(s : ℝ) / 4) ≤ 1 / 4) :
    ∃ (nA : ℕ → ℕ) (G : ∀ n : ℕ, RotGraph (Fin (nA n)) (Fin s → ZMod 2))
      (u : Fin (2 ^ (s / 2)) → Inner s s),
      (∀ η : ℝ, 0 < η → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → n ≤ nA n ∧ (nA n : ℝ) ≤ (1 + η) * n) ∧
      (∀ n : ℕ, (G n).LocallyInvertible ∧
        (G n).IsExpander ((((s : ℝ) ^ 2 - 1) * (2 : ℝ) ^ (-(s : ℝ) / 4)) ^ 2)) ∧
      Function.Injective u ∧
      (cayley u).IsExpander (((s : ℝ) ^ 2 - 1) * (2 : ℝ) ^ (-(s : ℝ) / 4)) ∧
      (∀ n t : ℕ, ((wrwSet (G n) u t).card : ℝ) ≤ (nA n : ℝ) * (2 : ℝ) ^ ((s : ℝ) * (s + (t : ℝ) / 2))) ∧
      (∀ (n t D : ℕ) (U : Fin (nA n) → Matrix (Fin D) (Fin D) ℝ),
        (∀ a, (U a)ᵀ = U a ∧ (U a)ᵀ * U a = 1) →
        ampThreshold (((s : ℝ) ^ 2 - 1) * (2 : ℝ) ^ (-(s : ℝ) / 4)) s t ≤
          opNorm (wrwAvg (G n) u t (prodU U)) ^ 2 →
        4 * (((s : ℝ) ^ 2 - 1) * (2 : ℝ) ^ (-(s : ℝ) / 4)) ≤ opNorm (avg U)) := by sorry

end ExpanderWalkDecode.Main
