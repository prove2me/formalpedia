-- Prove2me | Theorems.Thm_EditMulticoloring_Code_interval_restriction
-- name    : EditMulticoloring.Code.interval_restriction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T18:49:01.530201+00:00
-- url     : https://prove2.me/theorems/cb84f285-7ffd-4f7b-b2a1-4358040b77de
-- title:
--   Lemma 3 — Edit distance under contiguous interval restriction
-- statement:
--   Under the standing $q\ge2,t\ge1$ conventions, let $x,y\in A^n$, and let $1\le\ell_0\le\ell_1\le n$. Write $x_I,y_I$ for restriction to the same one-based contiguous interval $I=\{\ell_0,\ldots,\ell_1\}$. Then
--
--   $$d_E(x_I,y_I)\le d_E(x,y).$$
--
--   This includes every contiguous interval, including singleton intervals and those meeting either boundary. It supplies both prefix and suffix distance bounds in the decoder argument.
--
--   Differences from the source:
--   - encoding: finite words over an alphabet of q symbols and one-based positions → lists of Fin q, finite-coordinate functions for fixed lengths, and zero-based stored operations; reason: order-preserving conversion and the explicit interval formula preserve every source word and positioned edit
-- source:
--   Huiling Xie, Zitan Chen, Explicit Edit Codes via Multicoloring, STOC 2027 submission #819 (October 2026), Lemma 3, printed p. 5 (PDF p. 6), proof Appendix A, printed pp. 15–16 (PDF pp. 16–17); pinned repository artifact papers/stoc2027-819/source.pdf, SHA256 00172d5da76bf6bc886b8a1f87450befb76480107f54cb367988a065737eb376.

import Definitions.Def_EditMulticoloring_Code_Words

namespace EditMulticoloring.Code

theorem interval_restriction (q t : ℕ) (hq : 2 ≤ q) (ht : 1 ≤ t)
    (n lo hi : ℕ) (hlo : 1 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ n)
    (x y : Word q) (hx : x.length = n) (hy : y.length = n) :
    distance (interval x lo hi) (interval y lo hi) ≤ distance x y := by sorry

end EditMulticoloring.Code
