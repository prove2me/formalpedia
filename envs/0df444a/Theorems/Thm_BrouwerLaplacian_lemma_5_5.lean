-- Prove2me | Theorems.Thm_BrouwerLaplacian_lemma_5_5
-- name    : BrouwerLaplacian.lemma_5_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T17:00:07.061485+00:00
-- url     : https://prove2.me/theorems/e6cd5dc2-6ce2-425f-a4ac-d38f70684bc9
-- title:
--   Lemma 5.5 — routing inequality $|\langle x,v\rangle|\le\sum_{i<j}(1-|M_{ij}|)|x_i-x_j|$
-- statement:
--   Let $P$ be a real $n\times n$ orthogonal projection of rank $k$ with $P\mathbf 1=0$. Let $M$ be its matrix ($M_{ii}=0$, $M_{ij}=P_{ii}+P_{jj}-2P_{ij}-1$ for $i\ne j$) and $v=CM\mathbf 1$, where $C=I_n-\frac1nJ$. Then
--
--   1. for every $x\in\mathbb R^n$,
--   $$|\langle x,v\rangle|\le\sum_{i<j}(1-|M_{ij}|)\,|x_i-x_j|;$$
--   2. in particular,
--   $$\sum_{i<j}(1-|M_{ij}|)\,|v_i-v_j|\ge\|v\|^2.$$
--
--   The first inequality has the form of a capacitated routing bound on the complete graph with capacities $1-|M_{ij}|$; the second (take $x=v$) feeds Lemma 5.3 through Cauchy–Schwarz.
--
--   **Formalization Note** $\sum_{i<j}$ runs over pairs of indices of $\mathrm{Fin}\,n$ with $i<j$. The paper also names $N=CMC$ in the statement; $N$ does not appear in either conclusion.
--
--   Differences from the source:
--   - encoding: "Let $N=CMC$" in the statement → $N$ not mentioned; reason: $N$ occurs in neither conclusion; same instances
--   - encoding: indices $1,\dots,n$ → $\mathrm{Fin}\,n=\{0,\dots,n-1\}$; reason: relabeling; same instances
-- source:
--   P. K. Kothari, S. Tudose, On Brouwer's Laplacian conjecture, arXiv:2606.12197v1, Lemma 5.5, p.6

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_BrouwerLaplacian_routingM

namespace BrouwerLaplacian

open Finset Matrix

/-- **Lemma 5.5 (A Routing Inequality for M).**
Kothari, Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197v1, Lemma 5.5, p.6:
"Let P be an orthogonal projection of rank k which satisfies P1 = 0. Define the matrix M with
diagonal entries Mᵢᵢ = 0 and off-diagonal entries Mᵢⱼ = Pᵢᵢ + Pⱼⱼ − 2Pᵢⱼ − 1. Let N = CMC and
v = CM1. For any x ∈ ℝⁿ the following inequality holds
|⟨x, v⟩| ≤ Σ_{i<j} (1 − |Mᵢⱼ|) · |xᵢ − xⱼ|. In particular, Σ_{i<j} (1 − |Mᵢⱼ|)|vᵢ − vⱼ| ≥ ∥v∥²."

**Formalization Note.** `Σ_{i<j}` is over pairs of indices of `Fin n` with `i < j` (each
unordered pair once). `⟨x, v⟩ = Σᵢ xᵢvᵢ` and `‖v‖² = Σᵢ vᵢ²`. `N` is only named in the paper's
statement and does not occur in its conclusion. -/
theorem lemma_5_5 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    (∀ x : Fin n → ℝ, |∑ i, x i * routingV P i|
        ≤ ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |x i - x j|) ∧
    ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |routingV P i - routingV P j|
      ≥ ∑ i, routingV P i ^ 2 := by sorry

end BrouwerLaplacian
