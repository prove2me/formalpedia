-- Prove2me | Theorems.Thm_EditMulticoloring_Code_edit_ball_volume
-- name    : EditMulticoloring.Code.edit_ball_volume
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:48:35.789988+00:00
-- url     : https://prove2.me/theorems/bb792604-0f64-420c-9bbf-8c5f0e7cabf6
-- title:
--   Lemma 4 — Volume of an edit ball
-- statement:
--   Fix integers $q\ge2$ and $s\ge1$. For every $m\ge1$ and $x\in A^m$, the number of legal positioned scripts of length at most $s$, including the empty script and counting different scripts separately, satisfies
--
--   $$\#\mathrm{Scripts}_{\le s}(x)\le\sum_{i=0}^{s}(2q(m+s+1))^i,\qquad |B_s(x)|\le r_s(m).$$
--
--   The enumerated outputs are exactly all finite words at edit distance at most $s$, and
--
--   $$r_s(m)=\Theta_{q,s}(m^s).$$
--
--   The positive comparison constants and threshold are uniform over $m$ and $x$. This bounds confusion-graph neighborhoods when $s=2t$; it does not assert a matching lower bound for the ball itself.
--
--   Differences from the source:
--   - encoding: finite words over an alphabet of q symbols and one-based positions → lists of Fin q, finite-coordinate functions for fixed lengths, and zero-based stored operations; reason: order-preserving conversion and the explicit interval formula preserve every source word and positioned edit
--   - encoding: r_s(m) = Theta_(q,s)(m^s) → positive lower and upper comparison constants and a positive threshold chosen before m and x; reason: this expands the two-sided asymptotic notation for r_s, with dependence only on fixed q,s
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 4, printed p. 5 (PDF p. 6), proof Appendix B, printed p. 16 (PDF p. 17); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Words

namespace EditMulticoloring.Code

/-- Lemma 4, including script multiplicity, the metric ball, and the order of r_s. -/
theorem edit_ball_volume (q s : ℕ) (hq : 2 ≤ q) (hs : 1 ≤ s) :
    (∀ (m : ℕ) (hm : 1 ≤ m) (x : Word q), x.length = m →
      (scripts s x).length ≤ ∑ i ∈ Finset.range (s + 1), (2 * q * (m + s + 1)) ^ i ∧
      (∀ y : Word q, y ∈ ball s x ↔ distance x y ≤ s) ∧
      (ball s x).card ≤ radiusBound q s m) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      c * (m : ℝ) ^ s ≤ (radiusBound q s m : ℝ) ∧
      (radiusBound q s m : ℝ) ≤ C * (m : ℝ) ^ s) := by sorry

end EditMulticoloring.Code
