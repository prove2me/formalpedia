-- Prove2me | Theorems.Thm_DistAvgNOOT_lemma_5
-- name    : DistAvgNOOT.lemma_5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T13:38:43.527222+00:00
-- url     : https://prove2.me/theorems/9ad267e0-9ef2-45de-8a1f-179474cef0af
-- title:
--   Variance contraction of doubly stochastic averaging over a connected window
-- statement:
--   Let $A(0),A(1),\dots$ be $n\times n$ real matrices and $x(t+1)=A(t)x(t)$ for all $t\ge0$. Assume (Assumption 1 of the source) that every $A(t)$ is **doubly stochastic** (nonnegative entries, all row sums and all column sums equal to $1$), has **positive diagonal entries**, and that every positive entry satisfies $a_{ij}(t)\ge\eta$. Let
--
--   $$V(x)=\sum_{i=1}^n\Big(x_i-\frac1n\sum_{j=1}^nx_j\Big)^2$$
--
--   be the sample variance. Fix a window of times $t_0,\dots,t_0+B-1$ and suppose that the undirected graph on $\{1,\dots,n\}$ whose edges are the pairs $\{i,j\}$, $i\ne j$, with $a_{ij}(t)>0$ for some $t$ in the window is **connected**. Then
--
--   $$V\big(x(t_0+B)\big)\le\Big(1-\frac{\eta}{2n^2}\Big)V\big(x(t_0)\big).$$
--
--   This is Lemma 5 of the source, which is stated there for the windows $[kB,(k+1)B)$ under Assumption 3. Connectivity of the undirected union graph on the window implies Assumption 3 for that window (the argument of Lemma 3), and Lemma 5's proof uses only the window in question. So the statement is formalized for a single arbitrary window, with the connectivity hypothesis in Lemma 3's form. When $V(x(t_0))=0$ the claim is trivial; otherwise it is exactly the source's ratio bound $\frac{V(t_0)-V(t_0+B)}{V(t_0)}\ge\frac{\eta}{2n^2}$.
-- source:
--   A. Nedić, A. Olshevsky, A. Ozdaglar, J. N. Tsitsiklis, On Distributed Averaging Algorithms and Quantization Effects, IEEE Trans. Automat. Control 54(11), 2009; arXiv:0711.4179v2, Section 3.2, Lemma 5 (p. 12), together with Lemma 3 (p. 9) and Assumption 1 (p. 4). Cited as [34] Corollary 1 for Lemma 1 of Koshal-Nedić-Shanbhag arXiv:1605.00267v2.

import Mathlib

namespace DistAvgNOOT

/-- Nedić–Olshevsky–Ozdaglar–Tsitsiklis, Lemmas 3 and 5: over a window of `B` steps whose
union graph is connected, the sample variance contracts by the factor `1 - η / (2 n ^ 2)`. -/
theorem lemma_5 {n : ℕ} (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (η : ℝ)
    (hnn : ∀ t i j, 0 ≤ A t i j)
    (hrow : ∀ t i, ∑ j, A t i j = 1) (hcol : ∀ t j, ∑ i, A t i j = 1)
    (hdiag : ∀ t i, 0 < A t i i)
    (hη : ∀ t i j, 0 < A t i j → η ≤ A t i j)
    (t0 B : ℕ)
    (hconn : (⨆ t ∈ Finset.Ico t0 (t0 + B),
      SimpleGraph.fromRel (fun i j : Fin n => 0 < A t i j)).Connected)
    (x : ℕ → Fin n → ℝ) (hx : ∀ t, x (t + 1) = (A t).mulVec (x t)) :
    ∑ i, (x (t0 + B) i - (∑ j, x (t0 + B) j) / n) ^ 2 ≤
      (1 - η / (2 * (n : ℝ) ^ 2)) * ∑ i, (x t0 i - (∑ j, x t0 j) / n) ^ 2 := by
  sorry

end DistAvgNOOT
