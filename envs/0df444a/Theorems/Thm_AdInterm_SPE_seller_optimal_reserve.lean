-- Prove2me | Theorems.Thm_AdInterm_SPE_seller_optimal_reserve
-- name    : AdInterm.SPE.seller_optimal_reserve
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:27.531852+00:00
-- url     : https://prove2.me/theorems/5fba745d-cb09-4f14-8890-2b46e7fddddb
-- title:
--   Proof of Theorem 3.1, "Seller's Optimal Reserve", p. 37 — r*_{n+1} = φ^{-1}_{W_n}(0) maximizes E[max(r_S, W^{SH}) 1{W^{FH} ≥ r_S}]
-- statement:
--   Let $m\ge1$ bidders submit i.i.d. reports with law $W$, where $W\ge0$ has finite mean, is not a point mass at $0$, may have an atom at $0$, and its strictly positive part has a continuous, strictly positive density on its support (an interval with lower end $0$) and a strictly increasing virtual value. With $W^{\mathrm{FH}(m)}$, $W^{\mathrm{SH}(m)}$ the highest and second-highest reports ($W^{\mathrm{SH}(1)}=0$), a seller using reserve $r$ earns
--
--   $$
--   R(r)=\mathbb E\big[\max(r,W^{\mathrm{SH}(m)})\,\mathbf 1\{W^{\mathrm{FH}(m)}\ge r\}\big].
--   $$
--
--   Then $z_W\ge0$ and $R(r)\le R(z_W)$ for every $r\ge0$, where $z_W=\phi^{-1}_{W}(0)$, or $\phi^{-1}_{W\mid W>0}(0)$ when $W$ has an atom at $0$.
--
--   With $m=k_{n+1}$ and $W=W_n$ this is the seller's step of Theorem 3.1: $r^*_{n+1}=z_{W_n}$.
--
--   **Formalization Note** The virtual value is taken from the cdf at points $x>0$, where it equals that of the positive part. The reserve ranges over all of $\mathbb R_+$, as the seller's mechanism set on p. 12.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), proof of Theorem 3.1, "Seller's Optimal Reserve", p. 37

import Mathlib
import Definitions.Def_AdInterm_SPE_VirtualValue

open MeasureTheory

namespace AdInterm.SPE

theorem seller_optimal_reserve (m : ℕ) (hm : 1 ≤ m)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : RegularPos ν) (hνinc : IncVV ν) :
    0 ≤ zproj ν ∧
      ∀ r : ℝ, 0 ≤ r → sellerObj m ν r ≤ sellerObj m ν (zproj ν) := by sorry

end AdInterm.SPE
