-- Prove2me | Theorems.Thm_Arxiv2011_11825_output_intensity_expansion
-- name    : Arxiv2011_11825.output_intensity_expansion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T09:16:15.625452+00:00
-- url     : https://prove2.me/theorems/5b64657c-f3cc-5aa5-bc5f-b444302ade9e
-- title:
--   Eq. (2): self and interference terms of the output intensity
-- statement:
--   Let $t=(t_{mi})$ be a complex transmission matrix with $N$ columns, let $E^{\mathrm{in}}\in\mathbb{C}^N$ be an input field, and let $m$ be an output mode. Write $E_m^{\mathrm{out}}=\sum_{i=1}^N t_{mi}E_i^{\mathrm{in}}$ (eq. (1)), $a_i=t_{mi}E_i^{\mathrm{in}}$, and $a\cdot b=\mathrm{Re}(a\overline{b})$. Then the output intensity is
--
--   $$I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2=\sum_{i=1}^N|a_i|^2+\sum_{i=1}^N\sum_{\substack{j=1\\ j\ne i}}^N a_i\cdot a_j.$$
--
--   The paper reads the first sum as the contributions of the individual modulated input modes and the double sum as their mutual interference.
--
--   **Formalization Note** The paper writes the terms as $(t_{mi}E_i^{\mathrm{in}})^2$ and $t_{mi}E_i^{\mathrm{in}}\cdot t_{mj}E_j^{\mathrm{in}}$ for complex fields and calls them inner products. They are formalized as phasor inner products, $|a_i|^2$ and $\mathrm{Re}(a_i\overline{a_j})$, which is the reading under which the printed chain $I_m^{\mathrm{out}}=|E_m^{\mathrm{out}}|^2=(\sum_i a_i)^2=\cdots$ is true and the terms are intensity contributions. Read as complex multiplication, the link $|E_m^{\mathrm{out}}|^2=(E_m^{\mathrm{out}})^2$ would fail (one mode with $a_1=i$ gives $1\ne-1$).
-- source:
--   Guo, Zhang, Li and Pang, Sequential Transmission Matrix Evaluation Via Spatiotemporal Transmitted Modes Decomposition, arXiv:2011.11825v1 (2020), claim c018; Section 2, eq. (2) with eq. (1), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2011_11825_Basic

open Finset

namespace Arxiv2011_11825

theorem output_intensity_expansion {M N : ℕ} (t : Matrix (Fin M) (Fin N) ℂ) (E : Fin N → ℂ)
    (m : Fin M) :
    outIntensity t E m =
      (∑ i, Complex.normSq (amp t E m i)) +
        ∑ i, ∑ j ∈ univ.filter (fun j => j ≠ i),
          (amp t E m i * (starRingEnd ℂ) (amp t E m j)).re := by sorry

end Arxiv2011_11825
