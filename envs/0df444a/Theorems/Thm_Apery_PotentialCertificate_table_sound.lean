-- Prove2me | Theorems.Thm_Apery_PotentialCertificate_table_sound
-- name    : Apery.PotentialCertificate.table_sound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T15:07:42.35044+00:00
-- url     : https://prove2.me/theorems/55dcbbd5-ece1-46ba-b01c-0fe90b3d3145
-- title:
--   Soundness of rational certificates for the potential inequality
-- statement:
--   Let $C$ be any valid finite rational certificate table for the comparison measure and external field of Lemma 6.1, and let $L(C)$ and $R(C)$ be its outer endpoints. For every real $t$ satisfying $0<t$ and $L(C)\le t\le R(C)$,
--
--   $$2U_\rho(t)-V(t)\le M_0=-\frac{1329}{200}.$$
--
--   Here $U_\rho$ is the potential of the fixed sixteen-component comparison measure, $V$ is the external field, and validity means that all rational series bounds, square-root enclosures, weighted sums, interval-domain conditions, and joins pass the certificate predicate. The statement applies to tables of arbitrary size and connects arithmetic-only certificates to the original real-valued inequality.
-- source:
--   Derived rational-certificate encoding of mo271/Zeta5 at commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Table2/All.lean, potential_ineq_le_two (lines 4116–4120), and the U*.lean/I*.lean certificate files; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120. The certificate datatype and its generic soundness adapter are new formalization infrastructure.

import Definitions.Def_Zeta5_PotentialTableData
import Definitions.Def_Zeta5_SourceTable2Data
open Apery Apery.PotentialCertificate

theorem Apery.PotentialCertificate.table_sound (c : TableCertificate) (hc : c.Valid)
    (t : ℝ) (ht : 0 < t) (ht1 : (c.left : ℝ) ≤ t) (ht2 : t ≤ (c.right : ℝ)) :
    2 * Uρ t - Vfield t ≤ M0 := by sorry
