-- Prove2me | Theorems.Thm_DynConnWC_lemma_27
-- name    : DynConnWC.lemma_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:30:41.819253+00:00
-- url     : https://prove2.me/theorems/a48be45e-fd2e-4ec2-9672-332c50a6dd17
-- title:
--   Lemma 27 — Finner's read-two product inequality
-- statement:
--   Let $(\Omega_i,\mu_i)_{i\in\iota}$ be finitely many probability spaces, with product measure $\mu$. Let $f_1,\dots,f_s$ be measurable functions on the product with values in $[0,\infty]$, where each $f_t$ depends only on the coordinates in a set $A_t$, and each coordinate lies in at most two of the sets $A_t$. Then
--   $$\int\prod_{t=1}^sf_t\,d\mu\le\prod_{t=1}^s\Big(\int f_t^2\,d\mu\Big)^{1/2}.$$
--   This is the special case of Finner's generalized Hölder inequality in which every function has weight $1/2$. It replaces independence between searches in Lemma 11.
--
--   Differences from the source:
--   - encoding: nonnegative functions of independent random variables → measurable functions into $[0,\infty]$ on a product of probability spaces, integrated with `lintegral`; reason: the coordinates are the independent variables; no integrability condition is needed
--   - encoding: independent random variables → finitely many coordinates, each in an arbitrary probability space; reason: no generality is lost: group the variables by the set of (at most two) functions that use them; there are finitely many groups, the groups are independent, and each group is one coordinate whose space is the product of its variables' spaces
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 27, p.25 (PDF 26)

import Mathlib

set_option autoImplicit false

namespace DynConnWC

open MeasureTheory ENNReal Classical in
/-- **Lemma 27 (Read-two product inequality [Fin92]).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.25 (PDF 26).
"Let f_1, …, f_s be nonnegative functions of independent random variables, where each variable is
used by at most two of the functions. Then E[∏_{t=1}^{s} f_t] ≤ ∏_{t=1}^{s} (E[f_t²])^{1/2}."

**Formalization Note.** The independent variables are the coordinates of a finite product of
probability spaces. `f t` is measurable with values in `ℝ≥0∞` and depends only on the coordinates in
`A t`; each coordinate lies in at most two of the sets `A t`. Expectations are `lintegral`, so no
integrability condition is needed and an infinite right side is allowed. -/
theorem lemma_27 {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] {s : ℕ}
    (f : Fin s → (∀ i, Ω i) → ℝ≥0∞) (A : Fin s → Finset ι)
    (hf : ∀ t, Measurable (f t))
    (hdep : ∀ t (x y : ∀ i, Ω i), (∀ i ∈ A t, x i = y i) → f t x = f t y)
    (hread : ∀ i, ((Finset.univ : Finset (Fin s)).filter (fun t => i ∈ A t)).card ≤ 2) :
    ∫⁻ x, ∏ t, f t x ∂(Measure.pi μ) ≤
      ∏ t, (∫⁻ x, f t x ^ 2 ∂(Measure.pi μ)) ^ (1 / 2 : ℝ) := by sorry

end DynConnWC
