-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_C_4
-- name    : CorrelatedLocalSearch.Supplement.theorem_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:10:30.69419+00:00
-- url     : https://prove2.me/theorems/1b0265ff-e984-481a-af21-2e34da1462b7
-- title:
--   Theorem C.4 — unknown radius with an archived tape
-- statement:
--   The exact archived-tape portfolio, using one base walk and geometrically scheduled radius-$2^j$ Hamming-ball simulations, needs neither $h$ nor $D$. With $\ell_h=1+\lceil\log_2 h\rceil$ and $L=h+\log D+1$,
--   $$\Pr_\nu\{\sigma>T\}\le\min\{1,CD\lambda^h e^{-cT/(h^2\ell_h^2)}\},\qquad \mathbb E_\nu\sigma\le C\min\{\Psi_s(L),h^2\ell_h^2L\}.$$
--   The count includes all flips and restored coordinates; at most $2+\lceil\log_2n\rceil$ assignments and $\sigma$ archived symbols are kept, and every selector sees only its simulation's local history.
--
--   Differences from the source:
--   - encoding: ceiling base-two logarithms → `Nat.clog 2`; reason: identical on the positive $h$ and relevant $n$ in the theorem
--   - encoding: expectation of the possibly infinite total update count → an `ENNReal` lower Lebesgue integral of an infinity-valued natural count; reason: nonintegrability gives infinity rather than a default value
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem C.4, pp.31–32 (PDF pp.33–34)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_SAT

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem C.4, pp.31-32 (PDF pp.33-34).
The exact archived-tape geometric portfolio removes both radius and slack inputs, preserving the
base mean while adding a radius-free exponential tail and explicit update/storage accounting. -/
theorem theorem_C_4 (k r : Nat) (hk : k < 2 * r) (hr : r < k) :
    ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ n (Phi : List (CorrelatedLocalSearch.Clause k n)) (x0 : Fin n -> Bool),
        ∀ baseSelector : CorrelatedLocalSearch.Selector k n,
          CorrelatedLocalSearch.IsValidSelector Phi baseSelector ->
          ∀ localSelector : Nat -> CorrelatedLocalSearch.Selector k n,
            (∀ j ≤ Nat.clog 2 n,
              CorrelatedLocalSearch.IsValidSelector Phi (localSelector j)) ->
            ∃ A : ArchivedPortfolio k n Phi x0,
              A.baseSelector = baseSelector ∧ A.localSelector = localSelector ∧
              IsExactArchivedSchedule A ∧ A.simulatedAssignments ≤ 2 + Nat.clog 2 n ∧
              ∀ xs : Fin n -> Bool, CorrelatedLocalSearch.IsStrongWitness r Phi xs ->
                let h := hammingDist x0 xs
                1 ≤ h -> ∀ D : Real, 1 ≤ D ->
                  ∀ s, CorrelatedLocalSearch.sStar k r ≤ s -> s ≤ 1 ->
                    ∀ nu : Measure (Nat -> Fin k), nu ∈ CorrelatedLocalSearch.SourceClass k s D ->
                      let ellh := 1 + Nat.clog 2 h
                      let L := (h : Real) + Real.log D + 1
                      (∀ T : Nat, nu {omega | (T : ℕ∞) < portfolioSigma A omega} ≤
                        ENNReal.ofReal (min 1 (C * D * CorrelatedLocalSearch.lam k r ^ h *
                          Real.exp (-c * (T : Real) / ((h : Real) ^ 2 * (ellh : Real) ^ 2))))) ∧
                      (∫⁻ omega, ((portfolioSigma A omega : ℕ∞) : ENNReal) ∂nu) ≤
                        min (ENNReal.ofReal C * Psi k r s L)
                          (ENNReal.ofReal (C * (h : Real) ^ 2 * (ellh : Real) ^ 2 * L)) ∧
                      ∀ omega, portfolioArchiveSize A omega ≤ portfolioSigma A omega := by sorry

end CorrelatedLocalSearch.Supplement
