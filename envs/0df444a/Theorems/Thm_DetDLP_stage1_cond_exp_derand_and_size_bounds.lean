-- Prove2me | Theorems.Thm_DetDLP_stage1_cond_exp_derand_and_size_bounds
-- name    : DetDLP.stage1_cond_exp_derand_and_size_bounds
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:21.870397+00:00
-- url     : https://prove2.me/theorems/598138d4-36c9-4656-8e8c-c38d27144f14
-- title:
--   Stage I Conditional-Expectation Derandomization and Factor-Base Size Bounds
-- statement:
--   Establishes the mathematical and combinatorial components of Stage I (Section 3.1–3.2):
--
--   1. **Conditional expectation formula (eq. 3.5):** on any nonempty prefix slice $\Omega$, $\mathbb{E}[\Phi(S)\mid S\in\Omega] = (g_{\mathrm{ord}} J_\Omega + 64 B_\Omega - 128\mu A_\Omega + 64\mu^2|\Omega|)/(\mu^2|\Omega|)$;
--   2. **Greedy bit-fixing derandomization:** along any injective bit encoding of length $L$, inductive prefix selection maintains a chain $\Omega_0 \supseteq \dots \supseteq \Omega_L$ with non-increasing average and outputs $S \in \Omega$ satisfying $f(S) \le \mathbb{E}_{\Omega}[f]$;
--   3. **Block cardinality & native-address injectivity:** $|F_i(S)| \le T$ for $\mathbb{F}_p^*$, $|F_i(S)| \le 4T$ for general $E(\mathbb{F}_p)$, and $|F_i(S)| \le 2T$ for short Weierstrass curves ($p>2$);
--   4. **Total factor-base size bounds:** $\sum_i |F_i| = O(m^2 + m g_{\mathrm{ord}}^{1/m})$ in both the small-group regime and general regime (under Hasse's bound $|\#E(\mathbb{F}_p) - (p+1)| \le 2\sqrt{p}$).
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2, Theorem 3.1 proof (pp. 8–11)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Stage I conditional-expectation derandomization and block/total size bounds (Section 3.1–3.2):
(1) Exact conditional expectation formula (eq. 3.5) for `Φ(S)` restricted to any nonempty seed slice `Ω`;
(2) Prefix-partitioning greedy bit-fixing derandomization along any injective bit encoding of length `L`;
(3) Native-address injectivity and exact block cardinality bounds (`≤ T` for `F_p^*`, `≤ 4 T` for general `E(F_p)`, and `≤ 2 T` for short Weierstrass over `p > 2`);
(4) Total factor-base size bounds in both small-group and general regimes for `F_p^*` and `E(F_p)` (the latter under Hasse's bound). -/
theorem stage1_cond_exp_derand_and_size_bounds :
    (∀ {α : Type} [DecidableEq α] (Ω : Finset α) (W C : α → ℕ) (gord : ℕ) (μ : ℝ),
      Ω.Nonempty → μ ≠ 0 →
      (∑ S ∈ Ω, ((gord : ℝ) * (C S : ℝ) + 64 * ((W S : ℝ) - μ) ^ 2) / μ ^ 2) / (Ω.card : ℝ) =
        ((gord : ℝ) * ((∑ S ∈ Ω, C S : ℕ) : ℝ) +
          64 * ((∑ S ∈ Ω, (W S) ^ 2 : ℕ) : ℝ) -
          128 * μ * ((∑ S ∈ Ω, W S : ℕ) : ℝ) +
          64 * μ ^ 2 * (Ω.card : ℝ)) / (μ ^ 2 * (Ω.card : ℝ))) ∧
    (∀ {α : Type} [DecidableEq α] (L : ℕ) (enc : α → Fin L → Bool),
      Function.Injective enc →
      ∀ (Ω : Finset α) (f : α → ℝ), Ω.Nonempty →
        ∃ S ∈ Ω,
          (∀ k : ℕ, k ≤ L →
            ∃ Ωk : Finset α,
              Ωk.Nonempty ∧ Ωk ⊆ Ω ∧ S ∈ Ωk ∧
              (∀ x ∈ Ωk, ∀ j : Fin L, j.val < k → enc x j = enc S j) ∧
              (∑ x ∈ Ωk, f x) / (Ωk.card : ℝ) ≤ (∑ x ∈ Ω, f x) / (Ω.card : ℝ)) ∧
          f S ≤ (∑ x ∈ Ω, f x) / (Ω.card : ℝ)) ∧
    ((∀ (p m T : ℕ) [Fact p.Prime] (S : FpSeed p m) (i : Fin m),
        Set.InjOn
          (fun a : (ZMod p)ˣ => (((S i).1.val + 1) * (a : ZMod p).val + (S i).2.val) % p)
          (fpFactorBlock (p := p) T S i) ∧
        (fpFactorBlock (p := p) T S i).card ≤ T) ∧
     (∀ (p m T : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m),
        (ecFactorBlock E T S i).card ≤ 4 * T ∧
        (2 < p → E.a₁ = 0 → E.a₃ = 0 → (ecFactorBlock E T S i).card ≤ 2 * T))) ∧
    ((∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
        2 ≤ m → (∀ i : Fin m, (F i).Nodup) →
        ((¬(64 ≤ p - 1 ∧ 4096 * m ≤ p - 1) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
         (64 ≤ p - 1 ∧ 4096 * m ≤ p - 1 ∧
           ∃ S : FpSeed p m,
             ∀ i : Fin m, (F i).toFinset =
               fpFactorBlock (p := p) (hashThreshold p (p - 1) m (p - 1)) S i)) →
        ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
          (8193 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ)))) ∧
     (∀ (p m : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
        (F : Fin m → List E.toAffine.Point),
        3 < p → 2 ≤ m → (∀ i : Fin m, (F i).Nodup) →
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        |(gord : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) →
        ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
         (64 ≤ gord ∧ 4096 * m ≤ n ∧
           ∃ S : ECSeed p m,
             ∀ i : Fin m, (F i).toFinset =
               ecFactorBlock E (hashThreshold p n m gord) S i)) →
        ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
          (32772 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))))) := by sorry

end DetDLP
