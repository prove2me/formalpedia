-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_8
-- name    : DIObliviousTransfer.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:08:27.768709+00:00
-- url     : https://prove2.me/theorems/8fbed85a-21ec-4b2c-9a1e-511fbc6a13c9
-- title:
--   Lemma 8 — feasibility of the common schedule
-- statement:
--   Let $\gamma,\eta_{\mathrm{MS}}>0$ and let $N_0\ge\max\{166,200/(k\gamma)\}$ be an integer. The schedule (7)–(9), (26) has the following properties.
--
--   1. The noise and leakage thresholds are positive: $\nu,c_{\mathrm{local}},c_{\mathrm{global}},\nu_{\mathrm{global}}>0$.
--   2. The label-masking slack satisfies $\xi m-2\ell-3t_A-1>0.215m-4$ whenever $100\ell\le m$.
--   3. For all leakage and capacity functions $\ell(\lambda),q(\lambda)$, the label-masking error $2^{-(\xi m-2\ell-3t_A-1)/2}$, the hidden-payload error $2^{(3k^2m+1-\gamma L+2\ell+3km+c)/2}$ (for every constant $c\ge0$), the audit error $e^{-2(\eta_A-\kappa_{\mathrm{aud}})^2km}$, the test error $e^{-2(\eta_{\mathrm{MS}}-\kappa_{\mathrm{test}})^2t_A}$ and the erasure-size error are negligible.
--   4. The audit and decoder margins hold: $\eta_An\le m/40$ and $2\lfloor m/40\rfloor+\lfloor m/100\rfloor\le0.06m$.
--   5. An invocation of capacity $q$ has $L_q=\Theta(q+\ell+\log^2\lambda)$ coordinates.
--   6. The complete OT satisfies $L_{\mathrm{total}}=2L_{\mathrm{pre}}+L_0\le C_{\mathrm{size}}L_0=O(\ell+\log^2\lambda)$.
--   7. For each batch, $c_{\mathrm{global}}L_{\mathrm{total}}\le c_{\mathrm{local}}L_i\le m_i/100$ and $\nu_{\mathrm{global}}L_{\mathrm{total}}\le\nu L_i$.
--
--   This lemma is the parameter backbone of Theorems 6, 15 and 18.
--
--   Differences from the source:
--
--   - reading: L = Θ(ℓ + log² λ) → ∃ c₁ c₂ > 0, ∀ λ ≥ 2, ∀ ℓ: c₁(ℓ + log₂²λ) ≤ L ≤ c₂(ℓ + log₂²λ); reason: Decision D17: λ ≥ 2 since log₂²1 = 0; uniform in ℓ, the stronger reading
--   - reading: label-masking, hidden-payload, audit, test, and size errors are negligible; physical size Θ(q + ℓ + log² λ); a total budget meets every invocation's local budget → each phrase pinned to the bound its proof gives: 2^{−(ξm−2ℓ−3t_A−1)/2}, 2^{(3k²m+1−γL+2ℓ+3km+c)/2} for the O(1) constant c, exp[−2(η_A−κ_aud)²km], exp[−2(η_MS−κ_test)²t_A], the binomial erasure tail; c_global L_total ≤ c_local L_i ≤ m_i/100 and ν_global L_total ≤ ν L_i; reason: the printed sentences are informal; these are the quantities the proof (p.28) bounds
--   - encoding: uniform polynomial-time code operations → not restated: part of the CodeFamily.Spec interface (decision D15); reason: the operations belong to the code interface used by every protocol item
--   - generalization: γ, η_MS from Lemma 31 → any γ, η_MS > 0 (the arithmetic does not use the selector bound); reason: the lemma's clauses are arithmetic and hold for all positive constants; the paper's choice is a special case
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 8, p.27 (PDF p.29), with its proof p.28

import Mathlib
import Definitions.Def_DIObliviousTransfer_Ltotal

namespace DIObliviousTransfer

/-- **Lemma 8 (Feasibility of the common schedule)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421
(held version, sha256 8334c039…), p.27 (PDF p.29). For `γ, η_MS > 0` and an integer
`N₀ ≥ max{166, 200/(kγ)}`, the schedule (7)–(9), (26) has:
(a) positive noise and leakage thresholds `ν, c_local, c_global, ν_global > 0`;
(b) label-masking slack `ξm − 2ℓ − 3t_A − 1 > 0.215m − 4` whenever `100ℓ ≤ m`;
(c) negligible label-masking, hidden-payload, audit, test and size errors;
(d) the audit and decoder margins `η_A n ≤ m/40` and `2⌊m/40⌋ + ⌊m/100⌋ ≤ 0.06m`;
(e) physical size `L_q = Θ(q + ℓ + log² λ)` for an invocation of capacity `q`;
(f) `L_total = 2L_pre + L₀ ≤ C_size L₀ = O(ℓ + log² λ)`;
(g) a total physical-window budget `c_global L_total` meets each invocation's local budget
`c_local L_i ≤ m_i/100`, and `ν_global L_total ≤ ν L_i`, for each of the three batches.

**Formalization Note** (decisions D16, D17, and a reading). Each phrase of the lemma is the bound
its proof (p.28) establishes: the label-masking error is `2^{−(ξm−2ℓ−3t_A−1)/2}` (Lemmas 7, 13),
the hidden-payload error `2^{(3k²m+1−γL+2ℓ+3km+c)/2}` for the `O(1)` constant `c` of `b_pub`
((15)), the audit error `exp[−2(η_A−κ_aud)²km]` ((13)), the test error `exp[−2(η_MS−κ_test)²t_A]`
(Claim 1), and the size error the erasure tail of independent honest questions. These are stated
for arbitrary leakage and capacity functions `ℓ(λ)`, `q(λ)`. `Θ` is uniform in `q ≥ 1` and `ℓ`
for `λ ≥ 2`. The uniform polynomial-time code operations are the `CodeFamily.Spec` interface. -/
theorem lemma_8 (γ ηMS : ℝ) (N₀ : ℕ) (hγ : 0 < γ) (hη : 0 < ηMS) (hN1 : (166 : ℝ) ≤ N₀)
    (hN2 : 200 / (kk * γ) ≤ (N₀ : ℝ)) :
    -- (a)
    (0 < nuOf N₀ ηMS ∧ 0 < cLocal N₀ ∧ 0 < cGlobal N₀ ∧ 0 < nuGlobal N₀ ηMS) ∧
    -- (b)
    (∀ m ell : ℕ, 100 * ell ≤ m →
      0.215 * (m : ℝ) - 4 < xi * m - 2 * ell - 3 * tAOf m - 1) ∧
    -- (c)
    (∀ ell q : ℕ → ℕ,
      Negligible (fun lam => (2 : ℝ) ^ (-(xi * mOf lam (ell lam) (q lam) - 2 * ell lam -
        3 * tAOf (mOf lam (ell lam) (q lam)) - 1) / 2)) ∧
      (∀ c : ℝ, 0 ≤ c → Negligible (fun lam => (2 : ℝ) ^
        ((3 * kk ^ 2 * mOf lam (ell lam) (q lam) + 1 - γ * LOf N₀ (mOf lam (ell lam) (q lam)) +
          2 * ell lam + 3 * kk * mOf lam (ell lam) (q lam) + c) / 2))) ∧
      Negligible (fun lam => Real.exp (-2 * (etaA N₀ ηMS - kappaAud N₀ ηMS) ^ 2 *
        (kk * mOf lam (ell lam) (q lam)))) ∧
      Negligible (fun lam => Real.exp (-2 * (ηMS - kappaTest ηMS) ^ 2 *
        tAOf (mOf lam (ell lam) (q lam)))) ∧
      Negligible (fun lam => erasureTail N₀ (mOf lam (ell lam) (q lam)))) ∧
    -- (d)
    (∀ m : ℕ, etaA N₀ ηMS * nOf N₀ m ≤ (m : ℝ) / 40 ∧
      (2 * TOf m + eraseCap m : ℝ) ≤ 0.06 * m) ∧
    -- (e)
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ lam : ℕ, 2 ≤ lam → ∀ q ell : ℕ, 1 ≤ q →
      c₁ * (q + ell + Real.logb 2 lam ^ 2) ≤ (LOf N₀ (mOf lam ell q) : ℝ) ∧
      (LOf N₀ (mOf lam ell q) : ℝ) ≤ c₂ * (q + ell + Real.logb 2 lam ^ 2)) ∧
    -- (f)
    (∀ lam ell : ℕ, Ltotal N₀ lam ell ≤ Csize N₀ * L0Of N₀ lam ell) ∧
    (∃ c₂ : ℝ, 0 < c₂ ∧ ∀ lam : ℕ, 2 ≤ lam → ∀ ell : ℕ,
      (Ltotal N₀ lam ell : ℝ) ≤ c₂ * (ell + Real.logb 2 lam ^ 2)) ∧
    -- (g)
    (∀ lam ell : ℕ, ∀ mi : ℕ, mi = mPreOf N₀ lam ell ∨ mi = m0Of lam ell →
      cGlobal N₀ * Ltotal N₀ lam ell ≤ cLocal N₀ * LOf N₀ mi ∧
      cLocal N₀ * LOf N₀ mi ≤ (mi : ℝ) / 100 ∧
      nuGlobal N₀ ηMS * Ltotal N₀ lam ell ≤ nuOf N₀ ηMS * LOf N₀ mi) := by sorry

end DIObliviousTransfer
