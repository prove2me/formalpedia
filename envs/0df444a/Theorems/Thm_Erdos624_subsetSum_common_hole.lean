-- Prove2me | Theorems.Thm_Erdos624_subsetSum_common_hole
-- name    : Erdos624.subsetSum_common_hole
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:40:59.153103+00:00
-- url     : https://prove2.me/theorems/b278ca4e-bb2c-4b6a-a39c-78231c73bc8a
-- title:
--   Common holes for any fixed number of subset-sum-factor maps (Erdős 624)
-- statement:
--   Let $U$ be a set of $n=2^k$ elements, $V=\mathbb F_2^k$, and consider $r$ *subset-sum-factor* maps
--
--   $$g_i(A)=\psi_i\Bigl(\sum_{a\in A}v_i(a)\Bigr),\qquad v_i:U\to V,\ \psi_i:V\to U\ \text{arbitrary}.$$
--
--   **Theorem.** For every $r\ge0$ there is $k_0$ such that for all $k\ge k_0$ and all such maps $g_0,\dots,g_{r-1}$ there are a $k$-set $Y\subseteq U$ and a point $u\in U$ with
--
--   $$u\notin\bigcup_{i<r}\{g_i(A):A\subseteq Y\}.$$
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result, it would suffice to show that for each fixed number $r$ of maps $g_i:\mathcal P(U)\to U$, $|U|=2^k$, $k$ large, some $k$-set $Y$ and some $u\in U$ are missed by all $g_i$ on $\mathcal P(Y)$ (a *common hole*). This proves the fixed-$r$ common-hole statement for the structured class of subset-sum-factor maps (which includes affine subset-sum maps with arbitrary relabelling of outputs). It does not cover arbitrary maps and does not settle Problem 624.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^k)$, $V$ is `Fin k → ZMod 2`, tracks indexed by $\mathrm{Fin}\,r$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem subsetSum_common_hole (r : ℕ) : ∃ k0, ∀ k ≥ k0,
    ∀ (v : Fin r → Fin (2 ^ k) → (Fin k → ZMod 2)) (ψ : Fin r → (Fin k → ZMod 2) → Fin (2 ^ k)),
      ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧ ∃ u, ∀ i, ∀ A ⊆ Y, ψ i (∑ a ∈ A, v i a) ≠ u := by sorry

end Erdos624
