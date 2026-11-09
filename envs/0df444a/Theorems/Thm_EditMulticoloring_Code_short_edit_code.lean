-- Prove2me | Theorems.Thm_EditMulticoloring_Code_short_edit_code
-- name    : EditMulticoloring.Code.short_edit_code
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:49:51.009309+00:00
-- url     : https://prove2.me/theorems/ebf6fd7d-c01a-405c-baed-743d765be317
-- title:
--   Lemma 10 — The minimum-length greedy short edit code
-- statement:
--   Fix integers $q\ge2$ and $t\ge1$. For every $h\ge1$ the set in
--
--   $$\rho=\min\{\ell\ge h:q^\ell\ge q^h r_{2t}(\ell)\}$$
--
--   is nonempty, its minimum satisfies the inequality and is no larger than any other feasible length, and a positive constant depending only on $q,t$ bounds
--
--   $$h\le\rho\le h+C\log(h+1).$$
--
--   The lexicographic greedy table from Appendix C has at least the required $q^h$ selected words. Its first $q^h$ entries define an injective $E:A^h\to A^\rho$ whose image corrects every mixture of at most $t$ edits. The statement includes the output length, injectivity and disjoint edit balls. The short code protects the serialized color without assuming any of these guarantees.
--
--   Differences from the source:
--   - encoding: the minimum over integers ell at least h, with h at least 1 → the natural-number infimum with nonemptiness, membership and minimality all stated as conclusions; reason: the feasible integers are positive naturals, so their minimum is unchanged and the empty-set default cannot establish the result
--   - encoding: finite words over an alphabet of q symbols and one-based positions → lists of Fin q, finite-coordinate functions for fixed lengths, and zero-based stored operations; reason: order-preserving conversion and the explicit interval formula preserve every source word and positioned edit
--   - encoding: rho = h + O_(q,t)(log(h+1)) → one positive constant C before all h at least 1, with h at most rho and rho at most h + C log(h+1); reason: Appendix C explicitly enlarges the constant for the finitely many small h; the minimum gives the nonnegative overhead
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 10, printed p. 10 (PDF p. 11), proof Appendix C, printed pp. 16–17 (PDF pp. 17–18); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Construction

namespace EditMulticoloring.Code

theorem short_edit_code (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h →
      let ρ := shortLength q t h
      (∃ l : ℕ, h ≤ l ∧ q ^ h * radiusBound q (2 * t) l ≤ q ^ l) ∧
      (h ≤ ρ ∧ q ^ h * radiusBound q (2 * t) ρ ≤ q ^ ρ) ∧
      (∀ l : ℕ, h ≤ l → q ^ h * radiusBound q (2 * t) l ≤ q ^ l → ρ ≤ l) ∧
      ((ρ : ℝ) ≤ (h : ℝ) + C * Real.log (h + 1 : ℝ)) ∧
      (shortTable q t h).length = q ^ h ∧
      (∀ u : FixedWord q h, (shortEncode t h (toWord u)).length = ρ) ∧
      Function.Injective (fun u : FixedWord q h => shortEncode t h (toWord u)) ∧
      Corrects t (Set.range (fun u : FixedWord q h => shortEncode t h (toWord u)))
    := by sorry

end EditMulticoloring.Code
