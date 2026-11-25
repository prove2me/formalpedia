-- Prove2me | Theorems.Thm_Arxiv2011_11825_output_intensity_segment_regrouping
-- name    : Arxiv2011_11825.output_intensity_segment_regrouping
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:16:52.10926+00:00
-- url     : https://prove2.me/theorems/69a98980-6aa4-40c7-968a-ef3e443090dd
-- title:
--   Eq. (3): regrouping of the output intensity by input segments
-- statement:
--   Let $t=(t_{mi})$ be a complex transmission matrix with $N$ columns, let $E^{\mathrm{in}}\in\mathbb{C}^N$ be an input field, and let $m$ be an output mode. Let the $N$ input modes be divided into nonempty disjoint segments $Q_1,\dots,Q_k$ that together contain all $N$ modes. Write $a_i=t_{mi}E_i^{\mathrm{in}}$ and $a\cdot b=\mathrm{Re}(a\overline{b})$. Then the output intensity $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2$ satisfies
--
--   $$I_m^{\mathrm{out}}=\sum_{p=1}^k\Big[\sum_{i\in Q_p}|a_i|^2+\sum_{i\in Q_p}\sum_{\substack{j\in Q_p\\ j\ne i}}a_i\cdot a_j+\sum_{\substack{q=1\\ q\ne p}}^k\ \sum_{i\in Q_p}\sum_{j\in Q_q}a_i\cdot a_j\Big].$$
--
--   The bracket of segment $Q_p$ (eq. (3.p)) collects the intensity contributions of the modes in $Q_p$, the interference between modes inside $Q_p$, and the interference between modes in $Q_p$ and modes in every other segment. The paper concludes from this regrouping that the output intensity can be evaluated sequentially by input segments.
--
--   **Formalization Note** The paper writes the terms as $(t_{mi}E_i^{\mathrm{in}})^2$ and $t_{mi}E_i^{\mathrm{in}}\cdot t_{mj}E_j^{\mathrm{in}}$ for complex fields and calls them inner products. They are formalized as phasor inner products, $|a_i|^2$ and $\mathrm{Re}(a_i\overline{a_j})$, which is the reading under which the printed chain $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2=(\sum_i a_i)^2=\cdots$ is true and the terms are intensity contributions. Read as complex multiplication, the link $|E_m^{\mathrm{out}}|^2=(E_m^{\mathrm{out}})^2$ would fail (one mode with $a_1=i$ gives $1\ne-1$). The paper indexes the segments up to $k$ but their mode counts up to $N_z$; the statement uses one index set $\{1,\dots,k\}$ for both. Nonemptiness of the segments is the paper's implicit convention (each $Q_p$ has $N_p$ modes); the identity does not need it.
-- source:
--   Guo, Zhang, Li and Pang, Sequential Transmission Matrix Evaluation Via Spatiotemporal Transmitted Modes Decomposition, arXiv:2011.11825v1 (2020), claim c018; Section 2, eq. (3) (brackets (3.1)-(3.k)), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2011_11825_Basic

open Finset

namespace Arxiv2011_11825

theorem output_intensity_segment_regrouping {M N k : ℕ} (t : Matrix (Fin M) (Fin N) ℂ)
    (E : Fin N → ℂ) (m : Fin M) (seg : Fin N → Fin k) (hseg : Function.Surjective seg) :
    outIntensity t E m = ∑ p, segBracket t E m seg p := by sorry

end Arxiv2011_11825
