-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_4_5
-- name    : CorrelatedLocalSearch.Supplement.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:08:08.002757+00:00
-- url     : https://prove2.me/theorems/2b5bcaef-ebcc-4198-815d-81884a48c772
-- title:
--   Theorem 4.5 — restarting on leaving a Hamming ball
-- statement:
--   If a strong witness is at distance $1\le h\le H$ from $x_0$, reset an unsatisfying proposed assignment to $x_0$ whenever it leaves the radius-$2H$ ball, continuing with the next unused symbol. Uniformly over selectors and $\nu\in\mathcal Q_{s,D}$,
--   $$\Pr_\nu\{\tau_H>T\}\le\min\{1,CD\lambda^h e^{-cT/H^2}\},\qquad \mathbb E_\nu\tau_H\le C H^2(h+\log D+1).$$
--   The restoration-list implementation uses at most twice as many variable updates as source-driven flips.
--
--   Differences from the source:
--   - encoding: $O_{k,r}$ expectation → one positive constant quantified before all instances; reason: expands the uniform asymptotic statement
--   - encoding: expectation of a possibly infinite stopping time → an `ENNReal` lower Lebesgue integral of an infinity-valued natural stopping time; reason: nonintegrability gives infinity rather than a default value
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.5, pp.12–13 (PDF pp.14–15)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_SAT

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.5, pp.12-13 (PDF pp.14-15).
The observable radius-`2H` same-tape restart walk has an exponential tail, quadratic-radius mean,
and at most factor-two restoration overhead. -/
theorem theorem_4_5 (k r : Nat) (hk : k < 2 * r) (hr : r < k) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ n (Phi : List (CorrelatedLocalSearch.Clause k n)) (xs x0 : Fin n -> Bool),
        CorrelatedLocalSearch.IsStrongWitness r Phi xs ->
        let h := hammingDist x0 xs
        1 ≤ h -> ∀ H, h ≤ H ->
          ∀ sel, CorrelatedLocalSearch.IsValidSelector Phi sel ->
            ∀ D : Real, 1 ≤ D -> ∀ s, CorrelatedLocalSearch.sStar k r ≤ s -> s ≤ 1 ->
              ∀ nu : Measure (Nat -> Fin k), nu ∈ CorrelatedLocalSearch.SourceClass k s D ->
                (∀ T : Nat, nu {omega | (T : ℕ∞) < hammingRestartTau Phi sel x0 H omega} ≤
                  ENNReal.ofReal (min 1 (C * D * CorrelatedLocalSearch.lam k r ^ h *
                    Real.exp (-c * (T : Real) / (H : Real) ^ 2)))) ∧
                (∫⁻ omega, ((hammingRestartTau Phi sel x0 H omega : ℕ∞) : ENNReal) ∂nu) ≤
                  ENNReal.ofReal (C * (H : Real) ^ 2 * ((h : Real) + Real.log D + 1)) ∧
                ∀ (omega : Nat -> Fin k) (t : Nat),
                  (∀ j < t, ¬ CorrelatedLocalSearch.Satisfies Phi
                    (hammingRestartState Phi sel x0 H
                      (CorrelatedLocalSearch.tapePrefix omega j))) ->
                  hammingRestartUpdateCost Phi sel x0 H
                    (CorrelatedLocalSearch.tapePrefix omega t) ≤ 2 * t := by sorry

end CorrelatedLocalSearch.Supplement
