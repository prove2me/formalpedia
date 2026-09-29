-- Prove2me | Theorems.Thm_ErlerGross_midpoint_identity_A8
-- name    : ErlerGross.midpoint_identity_A8
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:20:10.61538+00:00
-- url     : https://prove2.me/theorems/9080718c-34a9-4bd9-86b9-e1f01bbd642b
-- title:
--   Midpoint identity (A.8): $\ln\frac{27}{16}+\sum_{n\ge1}3m_{2n}\beta_{2n}=0$
-- statement:
--   The midpoint identity (A.8) of Erler–Gross: $$0=\ln\frac{27}{16}+\sum_{n\ge1}3\,m_{2n}\beta_{2n},$$ where $m_{2n}=-\frac23\frac{A_{2n}}{\sqrt{2n}}$, $\beta_{2n}=\frac{\cos(n\pi)}{\sqrt{2n}}$ and $A_{2n}$ are the even coefficients in $\left(\frac{1+iz}{1-iz}\right)^{1/3}=1+\sum A_{2n}z^{2n}+i\sum A_{2n-1}z^{2n-1}$. Formally: the series $\sum_{n\ge1}3\,m_{2n}\beta_{2n}$ converges (absolutely) to $-\ln\frac{27}{16}$. Together with the other midpoint identities it guarantees that the cubic vertex in the lightcone basis contains no lightcone-time derivatives.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix A eq. (A.8), p. 37; proved in Appendix B, pp. 45-46

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem midpoint_identity_A8 :
    HasSum (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
      (-Real.log (27 / 16)) := by
  sorry

end ErlerGross
