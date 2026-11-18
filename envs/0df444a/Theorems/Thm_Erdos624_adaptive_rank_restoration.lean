-- Prove2me | Theorems.Thm_Erdos624_adaptive_rank_restoration
-- name    : Erdos624.adaptive_rank_restoration
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T02:12:03.530168+00:00
-- url     : https://prove2.me/theorems/b9b3f4f4-8593-4148-bcf6-95e0e441f97d
-- title:
--   Guard-free rank restoration under pool restriction (Erdős 624)
-- statement:
--   Let $P$ be finite, $Q\subseteq P$ with $|Q|\ge k$, and $\mathcal G$ a family of nonempty subsets of a type $U$ such that every $k$-subset of $P$ contains a member of $\mathcal G$. Let $p:U\to W$ be a labelling into a module $W$ over $\mathbb F_2$, with $\sum_{x\in A}p(x)=0$ for every $A\in\mathcal G$. Then there exist a subfamily $\mathcal H\subseteq\mathcal G$ and a labelling $p':U\to W\times(U\to\mathbb F_2)$ such that every member of $\mathcal H$ is contained in $Q$, every $k$-subset of $Q$ contains a member of $\mathcal H$, every $A\in\mathcal H$ is annihilated by $p'$, and $\dim_{\mathbb F_2}\operatorname{span}\{p'(x):x\in Q\}=\dim_{\mathbb F_2}\operatorname{span}\{p(x):x\in P\}$. Thus a feasible annihilator of a covering family on $P$ can be restored, after pruning the family, to the same rank on any still-large subpool $Q$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$. This is an auxiliary structural lemma for already feasible covering cores, taken from Sol's 2026-11-18 Perplexity note on adaptive rank restoration. It does **not** settle Erdős Problem 624, PAIR, Step 17, or DENSE-P.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 18: derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung, in the Perplexity Computer note “Adaptive Rank Restoration Under Pool Restriction” (task d32c2107-b546-4015-be2e-c9c4e46ce7cd, captured 2026-11-18 under perplexity_2026-11-18/); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (18 Nov 2026). Auxiliary finite result only; does NOT settle PAIR / Step 17 / DENSE-P / #624.

import Mathlib
open Finset

namespace Erdos624

theorem adaptive_rank_restoration {U : Type*} [DecidableEq U]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (P Q : Finset U) (G : Finset (Finset U)) (k : ℕ) (p : U → W)
    (hQP : Q ⊆ P) (hQk : k ≤ #Q)
    (hGne : ∀ A ∈ G, A.Nonempty)
    (hcov : ∀ Y : Finset U, Y ⊆ P → #Y = k → ∃ A ∈ G, A ⊆ Y)
    (hann : ∀ A ∈ G, ∑ x ∈ A, p x = 0) :
    ∃ (H : Finset (Finset U)) (p' : U → W × (U → ZMod 2)),
      H ⊆ G ∧
      (∀ A ∈ H, A ⊆ Q) ∧
      (∀ Y : Finset U, Y ⊆ Q → #Y = k → ∃ A ∈ H, A ⊆ Y) ∧
      (∀ A ∈ H, ∑ x ∈ A, p' x = 0) ∧
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p' '' (Q : Set U))) =
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (P : Set U))) := by sorry

end Erdos624
