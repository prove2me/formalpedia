-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_adaptive_cell_counting
-- name    : BirthdayEntropy.Soundness.adaptive_cell_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:49:50.257303+00:00
-- url     : https://prove2.me/theorems/a33c5c60-0a56-491b-8906-e7acc80de2d1
-- title:
--   Lemma 4.4 — Information-charged adaptive cell counting
-- statement:
--   Let $V$ be any finite set of $K$ points, let $r\ge0$ be an integer, and let $\Omega\subseteq V^r\times V^r$ be nonempty. Let $Q$ be uniform on $\Omega$, let $F$ be a deterministic finite cell map, let $R(f)\ge0$, and set $p=|\Omega|/K^{2r}$. For nonnegative $a,b,h,\kappa$, suppose
--   $$|\Omega_f|\le K^{2r}e^{-aR(f)},\qquad H_Q(F)\le\kappa I_Q(X_L;X_R)+b\mathbb E_QR(F)+h.$$
--   Then
--   $$(1+\kappa)\log(1/p)\ge(a-b)\mathbb E_QR(F)-h.$$
--   Moreover, for every real $R_0$, if $a\ge b$ and $R(f)\ge R_0$ in every occupied cell, then
--   $$(a-b)\mathbb E_QR(F)-h\ge(a-b)R_0-h.$$
--   The nonempty event ensures the ambient count is nonzero, including at $r=0$. This abstract information-charged counting statement applies independently of birthday graphs and retains its energy-floor clause.
--
--   Differences from the source:
--   - encoding: finite V and a nonempty subset of V^r times V^r → a finite type V, functions on Fin r, and an explicit nonempty finite subset; reason: this is an exact representation of the full ambient experiment, including r=0; Q, p and both marginals are computed
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.4, PDF pp8 / printed pp7

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Counting

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma 4.4 (3), PDF p8 / printed p7, including the energy-floor clause.
The ambient type is arbitrary finite V, and r=0 is allowed. -/
theorem adaptive_cell_counting {V τ : Type*} [Fintype V] [Fintype τ]
    (r : ℕ) (Ω : Finset ((Fin r → V) × (Fin r → V))) (hΩ : Ω.Nonempty)
    (F : ((Fin r → V) × (Fin r → V)) → τ) (R : τ → ℝ)
    (hR : ∀ f, 0 ≤ R f) (a b h κ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h) (hκ : 0 ≤ κ)
    (hcell : ∀ f, ((cell Ω F f).card : ℝ) ≤
      (Fintype.card V : ℝ)^(2*r) * Real.exp (-a * R f)) :
    let Q := uniformOn Ω hΩ
    let E := Q.mean (fun X => R (F X))
    let p := (Ω.card : ℝ) / (Fintype.card V : ℝ)^(2*r)
    (Q.map F).entropy ≤ κ * mutualInfo Q Prod.fst Prod.snd + b * E + h →
      (a-b) * E - h ≤ (1+κ) * Real.log (1/p) ∧
      ∀ R₀ : ℝ, b ≤ a →
        (∀ f, (cell Ω F f).Nonempty → R₀ ≤ R f) →
        (a-b) * R₀ - h ≤ (a-b) * E - h := by sorry

end BirthdayEntropy.Soundness
