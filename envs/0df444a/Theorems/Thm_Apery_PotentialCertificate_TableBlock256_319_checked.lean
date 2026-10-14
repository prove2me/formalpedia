-- Prove2me | Theorems.Thm_Apery_PotentialCertificate_TableBlock256_319_checked
-- name    : Apery.PotentialCertificate.TableBlock256_319.checked
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T15:10:07.620269+00:00
-- url     : https://prove2.me/theorems/2a6d713b-baa9-42e6-8535-95bb23908e07
-- title:
--   Checked potential-table certificates, intervals 256–319
-- statement:
--   Let $C_{256,319}$ be the stored rational certificate tree for intervals 256 through 319 of the 684-cell potential table. Every check in its validity predicate succeeds:
--
--   $$\operatorname{Valid}(C_{256,319}).$$
--
--   This includes the domain and series inequalities for the logarithm and arctangent bounds, the square-root enclosures, the sixteen weighted potential components, the interval-domain conditions, and overlap at every internal join. Each row's rational upper and lower bounds also satisfy
--
--   $$2u-v\le -\frac{1329}{200}.$$
--
--   The theorem is an arithmetic certificate; the generic soundness theorem supplies its real-analytic interpretation.
-- source:
--   Derived rational-certificate encoding of mo271/Zeta5 at commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Table2/All.lean, potential_ineq_le_two (lines 4116–4120), and the U*.lean/I*.lean certificate files; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120. The certificate datatype and its generic soundness adapter are new formalization infrastructure.

import Definitions.Def_Zeta5_PotentialTableBlock256_319Data

theorem Apery.PotentialCertificate.TableBlock256_319.checked : Apery.PotentialCertificate.TableBlock256_319.certificate.Valid := by sorry
