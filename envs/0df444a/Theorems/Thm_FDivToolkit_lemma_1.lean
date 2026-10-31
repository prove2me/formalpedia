-- Prove2me | Theorems.Thm_FDivToolkit_lemma_1
-- name    : FDivToolkit.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:59.805995+00:00
-- url     : https://prove2.me/theorems/0962d87d-756f-4682-be3e-1c185519c7fb
-- title:
--   Lemma 1 — $F$ is a valid divergence function
-- statement:
--   Let $H$ be a generating function and $F$ the function of (2). Then:
--
--   1. $F$ is strictly convex and continuously differentiable on $(0,\infty)$;
--   2. $F(1)=0$, $F'(1)=0$ and $\lim_{y\to\infty}F(y)/y=\infty$, that is, $F$ is cofinite;
--   3. $F\ge0$ on $(0,\infty)$, so $F$ attains its minimum $0$ at $1$;
--   4. $F(0)=\lim_{y\downarrow0}F(y)\in(0,\infty]$, and when $F(0)<\infty$ the extended $F$ is strictly convex on $[0,\infty)$;
--   5. if $H$ is continuously differentiable with $H'(0)=1$, then $F$ is twice continuously differentiable with $F''(1)=1$.
--
--   So $F$ defines a valid $F$-divergence, normalized when $H'(0)=1$.
--
--   Differences from the source:
--   - reading: F is strictly convex, continuously differentiable, for the F of (2) extended to [0, ∞) on p.5 → strict convexity on (0, ∞) and, when F(0) < ∞, on [0, ∞); C¹ and C² on the open half-line (0, ∞); reason: the slope of F at 0 is L, which may be −∞, so differentiability at 0 is not what the paper means; when F(0) = ∞ the extended inequality is trivially strict
--   - encoding: F(0) = lim_{y↓0} F(y) ∈ (0, ∞] (p.5), used by Lemma 1 → F0 is a supremum over (0, 1); added clauses: this is the limit at 0⁺ of F, and 0 < F0; reason: F decreases on (0, 1); the clauses record that the supremum is the paper's limit
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Lemma 1, p.6

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_Fh

open Filter Set
open scoped Topology ENNReal

namespace FDivToolkit

/-- Lemma 1, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.6, with the extension of
`F` to `[0, ∞)` of p.5: `F` is strictly convex, continuously differentiable and satisfies `F(1) = 0`,
`F′(1) = 0` and `lim_{y→∞} F(y)/y = ∞`; `F` is nonnegative, with minimum `0` at `1`; `F(0)` is the
limit of `F` at `0⁺` and lies in `(0, ∞]`; and if `H` is continuously differentiable with `H′(0) = 1`
then `F` is twice continuously differentiable with `F″(1) = 1`.

**Formalization Note.** Differentiability is on the open half-line `(0, ∞)`, where `F` is given
by (2). Strict convexity is stated on `(0, ∞)` and, when `F(0) < ∞`, on `[0, ∞)`; when `F(0) = ∞`,
the extended inequality is trivially strict. -/
theorem lemma_1 {H : ℝ → ℝ} (hH : IsAdmissibleH H) :
    StrictConvexOn ℝ (Ioi 0) (Fh H) ∧
    ContDiffOn ℝ 1 (Fh H) (Ioi 0) ∧
    Fh H 1 = 0 ∧
    deriv (Fh H) 1 = 0 ∧
    Tendsto (fun y => Fh H y / y) atTop atTop ∧
    (∀ y : ℝ, 0 < y → 0 ≤ Fh H y) ∧
    Tendsto (fun y => ENNReal.ofReal (Fh H y)) (𝓝[>] 0) (𝓝 (F0 H)) ∧
    0 < F0 H ∧
    (F0 H ≠ ⊤ → StrictConvexOn ℝ (Ici 0) fun y => if y = 0 then (F0 H).toReal else Fh H y) ∧
    (ContDiff ℝ 1 H → deriv H 0 = 1 →
      ContDiffOn ℝ 2 (Fh H) (Ioi 0) ∧ deriv (deriv (Fh H)) 1 = 1) := by sorry

end FDivToolkit
