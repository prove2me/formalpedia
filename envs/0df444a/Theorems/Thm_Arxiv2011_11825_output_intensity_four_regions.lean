-- Prove2me | Theorems.Thm_Arxiv2011_11825_output_intensity_four_regions
-- name    : Arxiv2011_11825.output_intensity_four_regions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:17:21.169601+00:00
-- url     : https://prove2.me/theorems/d50162e2-c84b-5822-b442-580d1b7a05a4
-- title:
--   Eq. (S1): the four-region regrouping of the output intensity
-- statement:
--   Let $t=(t_{mi})$ be a complex transmission matrix with $N$ columns, let $E^{\mathrm{in}}\in\mathbb{C}^N$ be an input field, and let $m$ be an output mode. Let the input modes be divided into four nonempty disjoint regions $Q_1,Q_2,Q_3,Q_4$ that together contain all $N$ modes. Write $a_i=t_{mi}E_i^{\mathrm{in}}$, $a\cdot b=\mathrm{Re}(a\overline{b})$ and, for regions $p,q$,
--
--   $$S_p=\sum_{i\in Q_p}|a_i|^2,\qquad A_p=\sum_{i\in Q_p}\sum_{\substack{j\in Q_p\\ j\ne i}}a_i\cdot a_j,\qquad C_{pq}=\sum_{i\in Q_p}\sum_{j\in Q_q}a_i\cdot a_j.$$
--
--   Then the output intensity $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2$ satisfies
--
--   $$I_m^{\mathrm{out}}=\big[S_1+A_1+C_{12}+C_{13}+C_{14}\big]+\big[S_2+A_2+C_{21}+C_{23}+C_{24}\big]+\big[S_3+A_3+C_{31}+C_{32}+C_{34}\big]+\big[S_4+A_4+C_{41}+C_{42}+C_{43}\big],$$
--
--   the four brackets being (S1.1)-(S1.4). This is eq. (3) for four segments, the case drawn in Fig. 1. Eq. (4) of the paper is the same display evaluated at the optimized input field $E^{\mathrm{in,opt}}$, so it is the instance $E^{\mathrm{in}}=E^{\mathrm{in,opt}}$ of this statement.
--
--   **Formalization Note** The paper writes the terms as $(t_{mi}E_i^{\mathrm{in}})^2$ and $t_{mi}E_i^{\mathrm{in}}\cdot t_{mj}E_j^{\mathrm{in}}$ for complex fields and calls them inner products. They are formalized as phasor inner products, $|a_i|^2$ and $\mathrm{Re}(a_i\overline{a_j})$, which is the reading under which the printed chain $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2=(\sum_i a_i)^2=\cdots$ is true and the terms are intensity contributions. Read as complex multiplication, the link $|E_m^{\mathrm{out}}|^2=(E_m^{\mathrm{out}})^2$ would fail (one mode with $a_1=i$ gives $1\ne-1$). The regions $Q_1,\dots,Q_4$ are the indices $0,1,2,3$ of $\mathrm{Fin}\,4$.
-- source:
--   Guo, Zhang, Li and Pang, Sequential Transmission Matrix Evaluation Via Spatiotemporal Transmitted Modes Decomposition, arXiv:2011.11825v1 (2020), claim c018; Supplement S1, eq. (S1) (brackets (S1.1)-(S1.4)), PDF p. 16; referred to in Section 2, PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2011_11825_Basic

open Finset

namespace Arxiv2011_11825

theorem output_intensity_four_regions {M N : ℕ} (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ)
    (m : Fin M) (seg : Fin N → Fin 4) (hseg : Function.Surjective seg) :
    outIntensity t E m =
      (selfTerm t E m seg 0 + intraTerm t E m seg 0 + crossTerm t E m seg 0 1 +
          crossTerm t E m seg 0 2 + crossTerm t E m seg 0 3) +
        (selfTerm t E m seg 1 + intraTerm t E m seg 1 + crossTerm t E m seg 1 0 +
          crossTerm t E m seg 1 2 + crossTerm t E m seg 1 3) +
        (selfTerm t E m seg 2 + intraTerm t E m seg 2 + crossTerm t E m seg 2 0 +
          crossTerm t E m seg 2 1 + crossTerm t E m seg 2 3) +
        (selfTerm t E m seg 3 + intraTerm t E m seg 3 + crossTerm t E m seg 3 0 +
          crossTerm t E m seg 3 1 + crossTerm t E m seg 3 2) := by sorry

end Arxiv2011_11825
