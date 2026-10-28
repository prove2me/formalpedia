-- Prove2me | Theorems.Thm_Erdos624_subsetSum_perturb
-- name    : Erdos624.subsetSum_perturb
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:40:58.267687+00:00
-- url     : https://prove2.me/theorems/7c8e99a7-e77a-462c-9aa5-3301aa41f193
-- title:
--   Perturbation version of the subset-sum-factor image bound (Erdős 624)
-- statement:
--   Let $U$ be a set of $n=2^k$ elements, $V=\mathbb F_2^k$, and consider $r$ *subset-sum-factor* maps
--
--   $$g_i(A)=\psi_i\Bigl(\sum_{a\in A}v_i(a)\Bigr),\qquad v_i:U\to V,\ \psi_i:V\to U\ \text{arbitrary}.$$
--
--   **Theorem.** Under the hypotheses of `subsetSum_finite` ($2td\le k$, $\binom{n-2t(d-1)}{t}>n^r$) there is a $k$-set $Y$ such that for **every** family of maps $f_0,\dots,f_{r-1}:\mathcal P(U)\to U$,
--
--   $$2^d\,\Bigl|\bigcup_{i<r}\{f_i(A):A\subseteq Y\}\Bigr|\le r\,2^k+2^d\sum_{i<r}e_i(Y),\qquad e_i(Y)=|\{A\subseteq Y: f_i(A)\ne g_i(A)\}|.$$
--
--   So a common hole persists for maps that agree with subset-sum-factor maps except on fewer than $(2^d-r)2^{k-d}$ subsets of $Y$ in total.
--
--   **Formalization Note.** $U=\mathrm{Fin}\,(2^k)$, $V$ is `Fin k → ZMod 2`, tracks indexed by $\mathrm{Fin}\,r$.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); definitions from Formal Conjectures 624.lean; (17) of claim from GPT 6.1 Sol (fifth answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem subsetSum_perturb (k r d t : ℕ) (hk : 2 * t * d ≤ k)
    (hc : (2 ^ k) ^ r < (2 ^ k - 2 * t * (d - 1)).choose t)
    (v : Fin r → Fin (2 ^ k) → (Fin k → ZMod 2)) (ψ : Fin r → (Fin k → ZMod 2) → Fin (2 ^ k)) :
    ∃ Y : Finset (Fin (2 ^ k)), #Y = k ∧
      ∀ g : Fin r → Finset (Fin (2 ^ k)) → Fin (2 ^ k),
        2 ^ d * #(((univ : Finset (Fin r)) ×ˢ Y.powerset).image (fun p => g p.1 p.2)) ≤
          r * 2 ^ k + 2 ^ d * ∑ i, #(Y.powerset.filter
            (fun A => g i A ≠ ψ i (∑ a ∈ A, v i a))) := by sorry

end Erdos624
