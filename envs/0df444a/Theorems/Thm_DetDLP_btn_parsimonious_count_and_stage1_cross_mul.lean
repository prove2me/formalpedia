-- Prove2me | Theorems.Thm_DetDLP_btn_parsimonious_count_and_stage1_cross_mul
-- name    : DetDLP.btn_parsimonious_count_and_stage1_cross_mul
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:18.66345+00:00
-- url     : https://prove2.me/theorems/fe2cc0de-c251-4462-98c5-fcaac3e4ff42
-- title:
--   Parsimonious BTN Counting, $s_{\mathrm{BTN}}$ Scaling, Stage I Cross-Multiplication, and Subcube Completion Counts
-- statement:
--   Establishes the four exact BTN-counting and Stage I prefix-derandomization identities:
--
--   1. **Parsimonious `{0,1}`-BTN exact counting:** for any parsimonious BTN $(G, T)$ encoding $R$ with $e_{\mathrm{net}} < P_0$, contracting over $\mathcal{B}_{P_0, 1}$ recovers the exact count $|R| < 2^{P_0}$;
--   2. **Theorem 2.2 scale parameter $s_{\mathrm{BTN}}$ (eq. 2.2):** $s_{\mathrm{BTN}} = \max(2, e_{\mathrm{net}}+1, \lceil \Delta_{\mathrm{net}}^{10/9}\rceil)$ satisfies $2 \le s_{\mathrm{BTN}}$, $e_{\mathrm{net}} < s_{\mathrm{BTN}}$, and $\Delta_{\mathrm{net}} \le \lceil s_{\mathrm{BTN}}^{9/10}\rceil$;
--   3. **Eq. (3.5) exact integer cross-multiplication:** comparing $\mathbb{E}[\Phi(S)\mid S\succeq \eta_0]$ and $\mathbb{E}[\Phi(S)\mid S\succeq \eta_1]$ with $\mu = (nT/p)^m$ is equivalent to the exact integer cross-multiplication inequality;
--   4. **Binary subcube prefix completion count:** the number of $b$-bit completions of an $r$-bit prefix $v$ in $[0, p)$ (resp. $[1, p)$) equals $\min((v+1)2^{b-r}, p) - \min(v 2^{b-r}, p)$ (resp. $\min((v+1)2^{b-r}, p) - \min(\max(v 2^{b-r}, 1), p)$).
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.2 eqs. (2.1)–(2.2) & Section 3.2 Proof of Theorem 3.1 (pp. 8, 13)

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

/-- BTN parsimonious counting, scale parameter `s_BTN`, Stage I conditional-expectation
integer cross-multiplication, and binary subcube completion counts (Section 2.2 eqs. 2.1–2.2 &
Section 3.2 p. 13):
(1) Contracting a parsimonious `{0, 1}`-valued BTN `(G, T)` over `TruncPoly P0 1` with `G.nE < P0`
recovers the exact satisfying-assignment count `(Finset.univ.filter R).card < 2 ^ P0`;
(2) Setting `s_BTN = max 2 (max (e_net + 1) ⌈Δ_net^{10/9}⌉)` satisfies `2 ≤ s_BTN`, `e_net < s_BTN`,
and `Δ_net ≤ ⌈s_BTN^{9/10}⌉`;
(3) Comparing `E[Φ(S) | S ⪰ η₀] ≤ E[Φ(S) | S ⪰ η₁]` in eq. (3.5) with `μ = (n T / p)^m` is
equivalent to the exact integer cross-multiplication inequality;
(4) The number of `b`-bit completions of an `r`-bit prefix `v` lying in `[0, p)` (resp. `[1, p)`)
is given by the closed-form subcube interval intersection cardinality. -/
theorem btn_parsimonious_count_and_stage1_cross_mul :
    (∀ (G : BipartiteMultigraph)
       (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
       {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
       (P0 : ℕ),
       IsParsimonious G T ext R →
       G.nE < P0 →
       (Finset.univ.filter R).card < 2 ^ P0 ∧
       BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
         truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card)) ∧
    (∀ (enet Δnet : ℕ),
       let sBTN : ℕ := max 2 (max (enet + 1) (Nat.ceil ((Δnet : ℝ) ^ ((10 : ℝ) / 9))))
       2 ≤ sBTN ∧ enet < sBTN ∧ Δnet ≤ Nat.ceil ((sBTN : ℝ) ^ ((9 : ℝ) / 10))) ∧
    (∀ (p n T m gord H₀ H₁ A₀ B₀ J₀ A₁ B₁ J₁ : ℕ),
       0 < p → 0 < n → 0 < T → 0 < H₀ → 0 < H₁ →
       let μ : ℝ := ((n : ℝ) * (T : ℝ) / (p : ℝ)) ^ m
       (((gord : ℝ) * (J₀ : ℝ) + 64 * (B₀ : ℝ) - 128 * μ * (A₀ : ℝ) + 64 * μ ^ 2 * (H₀ : ℝ)) /
           (μ ^ 2 * (H₀ : ℝ)) ≤
         ((gord : ℝ) * (J₁ : ℝ) + 64 * (B₁ : ℝ) - 128 * μ * (A₁ : ℝ) + 64 * μ ^ 2 * (H₁ : ℝ)) /
           (μ ^ 2 * (H₁ : ℝ))) ↔
       (((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₀ : ℤ) +
           64 * (p : ℤ) ^ (2 * m) * (B₀ : ℤ) -
           128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₀ : ℤ)) * (H₁ : ℤ) ≤
         ((p : ℤ) ^ (2 * m) * (gord : ℤ) * (J₁ : ℤ) +
           64 * (p : ℤ) ^ (2 * m) * (B₁ : ℤ) -
           128 * (p : ℤ) ^ m * ((n : ℤ) * (T : ℤ)) ^ m * (A₁ : ℤ)) * (H₀ : ℤ))) ∧
    (∀ (b r v p : ℕ), r ≤ b → p ≤ 2 ^ b →
       ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ u < p)).card =
         min ((v + 1) * 2 ^ (b - r)) p - min (v * 2 ^ (b - r)) p ∧
       ((Finset.range (2 ^ b)).filter (fun u => u / 2 ^ (b - r) = v ∧ 1 ≤ u ∧ u < p)).card =
         min ((v + 1) * 2 ^ (b - r)) p - min (max (v * 2 ^ (b - r)) 1) p) := by sorry

end DetDLP
