-- Prove2me | Theorems.Thm_BrouwerLaplacian_lemma_5_3
-- name    : BrouwerLaplacian.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:20.513323+00:00
-- url     : https://prove2.me/theorems/acb5c935-4f65-4951-a1fe-81b502cf7951
-- title:
--   Lemma 5.3 — $\sum_{i\ne j}(1-|M_{ij}|)^2\ge\frac2n\|v\|^2$, inequality (5.2)
-- statement:
--   Let $P$ be a real $n\times n$ orthogonal projection of rank $k$ with $P\mathbf 1=0$. Let $M$ be its matrix ($M_{ii}=0$, $M_{ij}=P_{ii}+P_{jj}-2P_{ij}-1$ for $i\ne j$) and $v=CM\mathbf 1$, where $C=I_n-\frac1nJ$. Then
--
--   $$\sum_{i\ne j}(1-|M_{ij}|)^2\ge\frac2n\,\|v\|^2.$$
--
--   The paper calls this the key technical ingredient: it is exactly the inequality (5.6) to which Lemma 5.6 reduces.
--
--   **Formalization Note** $\sum_{i\ne j}$ runs over ordered pairs of distinct indices. At $n=0$ both sides are empty sums.
--
--   Differences from the source:
--   - encoding: indices $1,\dots,n$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 5.3, p.5, eq. (5.2)

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_BrouwerLaplacian_routingM

namespace BrouwerLaplacian

open Finset Matrix

/-- **Lemma 5.3, inequality (5.2).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.3, p.5:
"Let P be an orthogonal projection of rank k which satisfies P1 = 0. Define the matrix M with
diagonal entries Mᵢᵢ = 0 and off-diagonal entries Mᵢⱼ = Pᵢᵢ + Pⱼⱼ − 2Pᵢⱼ − 1. Let v = CM1. Then
Σ_{i≠j} (1 − |Mᵢⱼ|)² ≥ 2/n ∥v∥². (5.2)"

**Formalization Note.** `Σ_{i≠j}` is over ordered pairs of distinct indices. At `n = 0` both
sides are empty sums (Lean's `2/0 = 0` is harmless). -/
theorem lemma_5_3 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    ∑ i, ∑ j with i ≠ j, (1 - |routingM P i j|) ^ 2
      ≥ (2 / (n : ℝ)) * ∑ i, routingV P i ^ 2 := by sorry

end BrouwerLaplacian
