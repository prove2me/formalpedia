-- Prove2me | Theorems.Thm_FixpReciprocal_SLReduces_trans
-- name    : FixpReciprocal.SLReduces_trans
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:12.162473+00:00
-- url     : https://prove2.me/theorems/1bfa6344-cee3-4184-8fc3-b55cad31419c
-- title:
--   Definition 3.2 (used in the proof of Theorem 4.2) — SL-reductions compose
-- statement:
--   If $\Pi$ admits an SL-reduction to $\Gamma$, and $\Gamma$ admits one to $\Delta$, then $\Pi$ admits an SL-reduction to $\Delta$. If $x_i=a_iy_{\rho(i)}+b_i$ and $y_l=a'_lz_{\rho'(l)}+b'_l$, the composed recovery is
--   $$x_i=a_ia'_{\rho(i)}\,z_{\rho'(\rho(i))}+a_ib'_{\rho(i)}+b_i.$$
--
--   The paper does not state this; it uses it to pass from the hardness of Lemma 3.4 to the hardness of the new gate set.
--
--   Differences from the source:
--
--   - reading: used silently in the proof of Theorem 4.2 → stated as its own theorem; reason: a step the proof relies on; no statement of the paper is changed
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Definition 3.2, p.10 (PDF p.12); used in the proof of Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_RealSearch
import Definitions.Def_FixpReciprocal_SLReduces

namespace FixpReciprocal

/-- **SL-reductions compose.** Not stated in the paper; it is what passes the hardness of Lemma 3.4 through the
reduction of the proof of Theorem 4.2 to every problem in FIXP.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.2, p.10 (the notion); proof of Theorem 4.2, p.12 (its use).

**Formalization Note.** The composed recovery is `x_i = (a_i a′_{ρ(i)}) y_{ρ′(ρ(i))} + (a_i b′_{ρ(i)} + b_i)`. -/
theorem SLReduces_trans {P Q R : RealSearch} (hPQ : SLReduces P Q) (hQR : SLReduces Q R) :
    SLReduces P R := by sorry

end FixpReciprocal
