-- Prove2me | Theorems.Thm_AsymSpecConn_theorem_2_4
-- name    : AsymSpecConn.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:54.696296+00:00
-- url     : https://prove2.me/theorems/ea7ae5f6-f946-4177-9ff1-97947be5827b
-- title:
--   Theorem 2.4 — $F_w$ is the spectral point extending an $\mathcal A$-good $w$
-- statement:
--   Let $\mathcal S$ be a Strassen semiring that is $\mathcal A$-decomposable and let $w:\mathcal A\to\mathbb R_{\ge0}$ be $\mathcal A$-good. Then:
--
--   1. $F_w\in\Delta$.
--   2. For every nonzero $s$, every $n\ge1$ and every $\mathcal A$-decomposition $a_1,\dots,a_q$ of $s^n$,
--   $$\max_{j\in[q]}w(a_j)\le F_w(s)^n\le\sum_{j=1}^q w(a_j).$$
--   3. $F_w=w$ on $\mathcal A$.
--   4. Every $g\in\Delta$ with $g\le w$ on $\mathcal A$ satisfies $g\le F_w$.
--   5. If $v:\mathcal S\to\mathbb R_{\ge0}$ satisfies $w\le v$ on $\mathcal A$, $v(st)=v(s)v(t)$, and $s\le t\Rightarrow v(s)\le v(t)$, then $F_w\le v$.
--   6. $F_w$ is the unique element of $\Delta$ that agrees with $w$ on $\mathcal A$.
--
--   So on an $\mathcal A$-decomposable semiring, spectral points correspond exactly to $\mathcal A$-good functions.
--
--   Differences from the source:
--
--   - encoding: F_w ∈ Δ, where F_w is valued in [0,∞] → a spectral point F whose values, coerced to [0,∞], are those of Fw; the further clauses are stated for F; reason: a Lean element of Δ has values in ℝ≥0, and such an F is unique
--   - encoding: w : A → ℝ≥0 → w : S → ℝ≥0 of which only the values on A are read; reason: the source applies its definitions to such functions through restriction (p.14); every w on A extends to S
--   - encoding: max_{j∈[q]} w(a_j) ≤ F_w(s)^n → w(a_j) ≤ F(s)^n for every j; reason: the same statement; for s ≠ 0 every A-decomposition of s^n is nonempty (p.13)
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Theorem 2.4, p.14

import Mathlib
import Definitions.Def_AsymSpecConn_IsStrassenSemiring
import Definitions.Def_AsymSpecConn_Spectrum
import Definitions.Def_AsymSpecConn_ALength
import Definitions.Def_AsymSpecConn_IsADecomposable
import Definitions.Def_AsymSpecConn_IsAGood
import Definitions.Def_AsymSpecConn_Fw

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn

/-- **Theorem 2.4** (p.14 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let S be A-decomposable and let
w : A → R≥0 be A-good. Then (i) Fw ∈ ∆. (ii) For every s ∈ S \ {0}, every n ≥ 1 and every
A-decomposition a1, …, aq of sⁿ, we have max_{j∈[q]} w(aj) ≤ Fw(s)ⁿ ≤ Σ_{j=1}^q w(aj).
(iii) Fw = w on A. (iv) Every g ∈ ∆ with g ≤ w on A satisfies g ≤ Fw. (v) Let v : S → R≥0 be such
that w ≤ v on A and such that for every s, t ∈ S, we have v(st) = v(s)v(t), and if s ≤ t, then
v(s) ≤ v(t). Then Fw ≤ v. (vi) Fw is the unique element of ∆ that agrees with w on A."

**Formalization Note** (i) is the existence of a spectral point `F` whose values, in `[0, ∞]`, are
those of `Fw`; (ii)–(vi) are stated for that `F`. `S` is a Strassen semiring (standing assumption
of §2, p.12). `w : S → ℝ≥0` with only its values on `A` used. In (ii) "max_j w(a_j) ≤ ·" is
"w(a_j) ≤ · for every j" (for `s ≠ 0` every A-decomposition of `sⁿ` is nonempty). -/
theorem theorem_2_4 {S : Type*} [CommSemiring S] (P : Preorder S)
    (hS : IsStrassenSemiring S P) (A : Set S) (hA : IsADecomposable P A) (w : S → ℝ≥0)
    (hw : IsAGood P A w) :
    ∃ F : ↥(Spectrum S P),
      (∀ s : S, ((F.1 s : ℝ≥0) : ℝ≥0∞) = Fw P A w s) ∧
      (∀ s : S, s ≠ 0 → ∀ n : ℕ, 1 ≤ n → ∀ (q : ℕ) (b : Fin q → S),
        IsADecomposition P A (s ^ n) q b →
          (∀ j, w (b j) ≤ F.1 s ^ n) ∧ F.1 s ^ n ≤ ∑ j, w (b j)) ∧
      (∀ a ∈ A, F.1 a = w a) ∧
      (∀ g : ↥(Spectrum S P), (∀ a ∈ A, g.1 a ≤ w a) → ∀ s, g.1 s ≤ F.1 s) ∧
      (∀ v : S → ℝ≥0, (∀ a ∈ A, w a ≤ v a) → (∀ s t, v (s * t) = v s * v t) →
        (∀ s t, P.le s t → v s ≤ v t) → ∀ s, F.1 s ≤ v s) ∧
      (∀ g : ↥(Spectrum S P), (∀ a ∈ A, g.1 a = w a) → g = F) := by sorry

end AsymSpecConn
