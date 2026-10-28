-- Prove2me | Theorems.Thm_Erdos624_supported_loss_rank_identity
-- name    : Erdos624.supported_loss_rank_identity
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:17:34.425535+00:00
-- url     : https://prove2.me/theorems/97f416cf-de7c-4e1d-9803-f3a35b58079c
-- title:
--   Supported-loss rank identity (ROOT): $\dim K(P)=|P|-|H|+\dim D(P)$ (Erdős 624)
-- statement:
--   Let $H\subseteq P$ be finite, $\mathcal F$ a finite family of inputs $A\subseteq P$, and for each exterior point $x\in P\setminus H$ a repair $R_x\in\mathcal F$ with $x\in R_x\subseteq H\cup\{x\}$. Let $K(P)=\operatorname{span}_{\mathbb F_2}\{\chi_A:A\in\mathcal F\}$ and define the homogeneous root defect $\delta(A)=\chi_{A\cap H}+\sum_{x\in A\setminus H}\chi_{R_x\setminus\{x\}}\in\mathbb F_2^H$, $D(P)=\operatorname{span}\{\delta(A):A\in\mathcal F\}$. **Theorem (ROOT).** $\dim K(P)+|H|=|P|+\dim D(P)$; with $|H|=k-1$ this is $\rho(P)=|P|-\dim K(P)=k-1-\dim D(P)$.
--
--   (In Lean, $\delta(A)(h)=[h\in H]\,(\chi_A(h)+\sum_{x\in P\setminus H}\chi_A(x)\chi_{R_x}(h))$, which equals the formula above since $R_x\setminus\{x\}\subseteq H$.)
--
--   Source: 'Supported-Loss Localization and Actual-Parent Packings', (ROOT).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes (outside coverage / core erasure, best dense cores, near-saturation, witness backbone, supported-loss localization, unrooted mixed-layer cores, polynomial subpools) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem supported_loss_rank_identity {U : Type*} [DecidableEq U] (H P : Finset U) (hHP : H ⊆ P)
    (F : Finset (Finset U)) (hF : ∀ A ∈ F, A ⊆ P) (R : U → Finset U)
    (hR : ∀ x ∈ P \ H, R x ∈ F ∧ x ∈ R x ∧ R x ⊆ insert x H) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun y => if y ∈ A then (1 : ZMod 2) else 0}) + #H =
      #P + Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        {g | ∃ A ∈ F, g = fun h => if h ∈ H then
          ((if h ∈ A then (1 : ZMod 2) else 0) +
            ∑ x ∈ P \ H, (if x ∈ A then (1 : ZMod 2) else 0) * (if h ∈ R x then 1 else 0))
          else 0}) := by sorry

end Erdos624
