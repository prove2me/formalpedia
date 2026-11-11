-- Prove2me | Theorems.Thm_CaiFourierSparse_Learning_theorem_4_3
-- name    : CaiFourierSparse.Learning.theorem_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:15:26.637249+00:00
-- url     : https://prove2.me/theorems/91bebdf0-7909-43ab-9d0c-7e58d5210d5c
-- title:
--   Theorem 4.3 — the Haar–Fourier basis: analytic sparsity, $L^2$ and weighted $\ell^\infty$ approximation, and conditioning
-- statement:
--   Let $\mathcal B$ be the Haar–Fourier basis of Definition 4.1 with $K=2^a\ge k$, $N=2^b\ge2F$ and $K\mid2N$. For every ratio bound $c\ge1$ (the paper's $K=O(k)$) there is a constant $C>0$ such that for every $k$-Fourier-sparse $x$ with frequencies in $[-F,F]$:
--
--   1. the coefficients $\alpha_H=\langle x,\varphi_H\rangle_{[-1,1]}$ are analytically sparse: $\sum_H|\alpha_H|\le C\sqrt k\,\log N\,\big(\sum_H|\alpha_H|^2\big)^{1/2}$ (eq. (16));
--   2. if $N\ge2F+Ck^2/\delta^2$, then $\|P_Nx-x\|_{[-1,1]}\le\delta\|x\|_{[-1,1]}$;
--   3. with $\iota^\perp=\iota-P_N\iota$ and $g_N=P_Nx+\frac{x(1)-x(-1)}2\iota^\perp$: if $N\ge C(F+k^2)\sqrt{\log k}/\delta$, then $\max_{t\in[-1,1]}|x(t)-g_N(t)|/\sqrt{D_k(t)}\le\delta\|x\|_{[-1,1]}$;
--   4. every $\varphi_H\in\mathcal B$ and $\iota^\perp$ are well conditioned with respect to $D_k$: if $K\le ck$, then $\max_{t\in[-1,1]}|\varphi_H(t)|/\sqrt{D_k(t)}\le C\sqrt{\log 2k}$; if $N\ge k^2$, then $\max_{t\in[-1,1]}|\iota^\perp(t)|/\sqrt{D_k(t)}\le C\sqrt{\log2k}/k$; and $|\varphi_H(t)|\le C\min\{\sqrt{|H|},1/(\sqrt{|H|}(1-|t|))\}$.
--
--   The logarithms are stated as printed. Clause 4 carries the two conditions under which the paper uses it: $K=O(k)$ (§3: "We pick $K=O(k)$"; proof of Property 4, printed p. 23 / PDF p. 25: "$|H|\le K<2k$") and $N\ge k^2$ (same proof: "the choice of the cutoff ensures $N\ge k^2$"; the theorem says "with different $N$"). Without them clause 4 is false (INSIGHTS I5).
--
--   Differences from the source:
--   - encoding: B with K ≥ k and N ≥ 2F powers of two, K | 2N → exponents a, b with k ≤ 2^a, 2F ≤ 2^b, a ≤ b + 1; clause 4, which involves neither x nor F, is quantified over every such (a, b); reason: Lean representation of the powers of two; F = 0 makes every N admissible, so clause 4 loses nothing
--   - reading: clause 4, |φ_H(t)|/√D_k(t) = O(√log 2k) for B with any 2-power K ≥ k → the bound for K ≤ c·k, for every c ≥ 1 (C depends on c; clauses 1–3 do not involve c); reason: the paper picks K = O(k) (§3, PDF p. 10) and its proof of Property 4 uses |H| ≤ K < 2k (PDF p. 25); for K ≫ k the bound fails (INSIGHTS I5)
--   - reading: clause 4, |ι⊥(t)|/√D_k(t) = O(√log 2k / k) (no N condition printed; 'with different N') → the bound for N ≥ k²; reason: the proof of Property 4 states 'the choice of the cutoff ensures N ≥ k²' (PDF p. 25); for N of order k the bound fails (INSIGHTS I5)
--   - encoding: ‖P_N x − x‖_{[-1,1]} ≤ δ‖x‖_{[-1,1]} → ‖P_N x − x‖² ≤ δ²‖x‖² (energies in ℝ≥0∞); reason: equivalent for δ > 0
--   - encoding: max over t ∈ [−1,1] of a ratio ≤ bound → the ratio ≤ bound for every t ∈ [−1,1]; reason: the maximum of a continuous function on [−1,1] is attained; equivalent
--   - encoding: |φ_H(t)| = O(1)·min{√|H|, 1/(√|H|(1−|t|))} → |φ_H(t)| ≤ C√|H| and |φ_H(t)|·√|H|·(1−|t|) ≤ C on [−1,1]; reason: equivalent with 1/0 = ∞ at t = ±1; avoids Lean's 1/0 = 0
--   - encoding: O(·) and 'for a universal constant C' → one constant C > 0, fixed before all parameters, for the O(·) bounds and the cutoffs of clauses 2 and 3; reason: the source uses one universal C (with different N)
-- source:
--   Cai, Chen, Shao, Wang (2026), Learning Fourier-Sparse Signals and Multiband Signals, arXiv:2609.02977 (supplied manuscript, SHA-256 0ce139ab…), Theorem 4.3, printed p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_CaiFourierSparse_Learning_Signal
import Definitions.Def_CaiFourierSparse_Learning_HaarFourier

namespace CaiFourierSparse.Learning

/-- Theorem 4.3 (printed p. 13, PDF p. 15). The Haar–Fourier basis `B` (`N = 2^b ≥ 2F`,
`K = 2^a ≥ k`, `K ∣ 2N`) satisfies, for one universal constant `C`:
(1) `∑_H |α_H| ≤ C √k log N (∑_H |α_H|²)^{1/2}` for `α_H = ⟨x, φ_H⟩`;
(2) if `N ≥ 2F + C k²/δ²` then `‖P_N x - x‖_{[-1,1]} ≤ δ ‖x‖_{[-1,1]}`;
(3) if `N ≥ C (F + k²) √(log k)/δ` then `max_{t∈[-1,1]} |x(t) - g_N(t)|/√(D_k(t)) ≤ δ ‖x‖`;
(4) `|φ_H(t)|/√(D_k(t)) ≤ C √(log 2k)` when `K = O(k)` (`K ≤ c k` for the given ratio `c`;
§3 "We pick K = O(k)", proof of Property 4 "|H| ≤ K < 2k"), `|ι⊥(t)|/√(D_k(t)) ≤ C √(log 2k)/k`
when `N ≥ k²` (proof of Property 4: "the choice of the cutoff ensures N ≥ k²"), and
`|φ_H(t)| ≤ C min{√|H|, 1/(√|H| (1 - |t|))}` on `[-1,1]`. -/
theorem theorem_4_3 :
    ∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, 0 < C ∧
      (∀ (F : ℝ) (k a b : ℕ), 0 ≤ F → 1 ≤ k → k ≤ 2 ^ a → 2 * F ≤ 2 ^ b → a ≤ b + 1 →
        ∀ (α : Fin k → ℂ) (f : Fin k → ℝ), Bandlimited F f →
          ∑ H ∈ haarIdxSet b a, ‖hfCoeff b a (sparseSignal α f) H‖ ≤
            C * Real.sqrt k * Real.log ((2 : ℝ) ^ b) *
              Real.sqrt (∑ H ∈ haarIdxSet b a, ‖hfCoeff b a (sparseSignal α f) H‖ ^ 2)) ∧
      (∀ (F δ : ℝ) (k a b : ℕ), 0 ≤ F → 0 < δ → 1 ≤ k → k ≤ 2 ^ a → a ≤ b + 1 →
        2 * F + C * (k : ℝ) ^ 2 / δ ^ 2 ≤ 2 ^ b →
        ∀ (α : Fin k → ℂ) (f : Fin k → ℝ), Bandlimited F f →
          wsq (fun t => projN (2 ^ b) (sparseSignal α f) t - sparseSignal α f t) ≤
            ENNReal.ofReal (δ ^ 2) * wsq (sparseSignal α f)) ∧
      (∀ (F δ : ℝ) (k a b : ℕ), 0 ≤ F → 0 < δ → 1 ≤ k → k ≤ 2 ^ a → 2 * F ≤ 2 ^ b →
        a ≤ b + 1 → C * ((F + (k : ℝ) ^ 2) * Real.sqrt (Real.log k) / δ) ≤ 2 ^ b →
        ∀ (α : Fin k → ℂ) (f : Fin k → ℝ), Bandlimited F f →
          ∀ t ∈ window, ‖sparseSignal α f t - gN (2 ^ b) (sparseSignal α f) t‖ /
              Real.sqrt (Dk k t) ≤ δ * wnorm (sparseSignal α f)) ∧
      (∀ (k a b : ℕ), 1 ≤ k → k ≤ 2 ^ a → a ≤ b + 1 →
        (∀ H ∈ haarIdxSet b a, ∀ t ∈ window,
          ((2 : ℝ) ^ a ≤ c * k →
            ‖phiH b a H t‖ / Real.sqrt (Dk k t) ≤ C * Real.sqrt (Real.log (2 * k))) ∧
          ‖phiH b a H t‖ ≤ C * Real.sqrt (haarSupp a H) ∧
          ‖phiH b a H t‖ * (Real.sqrt (haarSupp a H) * (1 - |t|)) ≤ C) ∧
        ((k : ℝ) ^ 2 ≤ 2 ^ b → ∀ t ∈ window,
          ‖iotaPerp (2 ^ b) t‖ / Real.sqrt (Dk k t) ≤ C * Real.sqrt (Real.log (2 * k)) / k)) := by sorry

end CaiFourierSparse.Learning
