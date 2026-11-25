-- Prove2me | Theorems.Thm_DeficitAtMax
-- name    : DeficitAtMax
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:26:48.98159+00:00
-- url     : https://prove2.me/theorems/98344114-067a-4597-bf2f-4d58e4ad1d7b
-- title:
--   Deficit At Max: Deficit At Max
-- statement:
--   The deficit estimate at the maximum point: `p ≤ n`, the two-sided bound
--   `0 ≤ d_v ≤ (n-p) m (m-1)`, and the paper's latitude bound eq:latitude together
--   with `a > 8/13`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitAtMax.lean#L14-L212
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitAtMax.lean#L14-L212

module
public import Definitions.Def_PHarmonicPoly_TraceIdentity
public import Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Definitions.Def_PHarmonicPoly_DeficitBound
public import Definitions.Def_PHarmonicPoly_DeficitAtMax
public import Theorems.Thm_DeficitBound
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_GreatCircleTrigPoly
public import Theorems.Thm_TraceIdentity

set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial

theorem DeficitAtMax {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) {p : ℝ}
    (hp : (n : ℝ) - 1 / 13 ≤ p)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1)
    (hE : EpAlg p P = 0) :
    p ≤ (n : ℝ) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
        0 ≤ iteratedFDeriv ℝ 2
              (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
              ![v, v] + (m : ℝ) * ((m : ℝ) - 1)
        ∧ iteratedFDeriv ℝ 2
              (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
              ![v, v] + (m : ℝ) * ((m : ℝ) - 1)
            ≤ ((n : ℝ) - p) * ((m : ℝ) * ((m : ℝ) - 1))
        ∧ -1 ≤ MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
                EuclideanSpace ℝ (Fin n)) i) P
        ∧ MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
                EuclideanSpace ℝ (Fin n)) i) P
            ≤ -1 + Real.pi ^ 2 * ((n : ℝ) - p) / 2
        ∧ 8 / 13 < -(MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
                EuclideanSpace ℝ (Fin n)) i) P) := by sorry
