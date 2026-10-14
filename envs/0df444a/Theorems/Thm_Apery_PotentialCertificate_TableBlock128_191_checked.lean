-- Prove2me | Theorems.Thm_Apery_PotentialCertificate_TableBlock128_191_checked
-- name    : Apery.PotentialCertificate.TableBlock128_191.checked
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T15:09:59.974525+00:00
-- url     : https://prove2.me/theorems/b4d8dc96-6a0c-44f0-a973-fc40fbba4533
-- title:
--   Checked potential-table certificates, intervals 128–191
-- statement:
--   Let $C_{128,191}$ be the stored rational certificate tree for intervals 128 through 191 of the 684-cell potential table. Every check in its validity predicate succeeds:
--
--   $$\operatorname{Valid}(C_{128,191}).$$
--
--   This includes the domain and series inequalities for the logarithm and arctangent bounds, the square-root enclosures, the sixteen weighted potential components, the interval-domain conditions, and overlap at every internal join. Each row's rational upper and lower bounds also satisfy
--
--   $$2u-v\le -\frac{1329}{200}.$$
--
--   The theorem is an arithmetic certificate; the generic soundness theorem supplies its real-analytic interpretation.
-- source:
--   Derived rational-certificate encoding of mo271/Zeta5 at commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Table2/All.lean, potential_ineq_le_two (lines 4116–4120), and the U*.lean/I*.lean certificate files; https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Table2/All.lean#L4116-L4120. The certificate datatype and its generic soundness adapter are new formalization infrastructure.

import Definitions.Def_Zeta5_PotentialTableBlock128_191Data

theorem Apery.PotentialCertificate.TableBlock128_191.checked : Apery.PotentialCertificate.TableBlock128_191.certificate.Valid := by sorry
