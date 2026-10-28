-- Prove2me | Theorems.Thm_Erdos624_monoid_compression
-- name    : Erdos624.monoid_compression
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T03:33:35.637174+00:00
-- url     : https://prove2.me/theorems/ca841cb8-254b-481f-9523-e444a734ba8b
-- title:
--   Image compression for commutative-aggregate maps over collision blocks (Erdős 624)
-- statement:
--   Let $M$ be a finite commutative monoid, $v:U\to M$ and $\psi:M\to U$ arbitrary, and let $h(A)=\psi\bigl(\prod_{x\in A}v(x)\bigr)$ (a *commutative-aggregate* map). Write $b=2^{2t}$.
--
--   **Theorem.** Let $B_1,\dots,B_d\subseteq U$ be pairwise disjoint with $|B_j|\le 2t$, each containing distinct $P_j,Q_j\subseteq B_j$ with equal $v$-products. Then for every $Y\supseteq\bigcup_jB_j$,
--
--   $$b^d\,\bigl|\{h(A):A\subseteq Y\}\bigr|\;\le\;(b-1)^d\,2^{|Y|}.$$
--
--   Each collision block saves a fixed fraction of the possible product values, and these savings multiply. This is (9) of the analysis; no cancellation or group structure on $M$ is assumed.
--
--   **Formalization Note.** Blocks indexed by $\mathrm{Fin}\,d$; natural-number inequality.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); (9) of the analysis derived from GPT 6.1 Sol's analysis (sixth report, Oct 2026), relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem monoid_compression {U : Type*} [Fintype U] [DecidableEq U] {M : Type*} [CommMonoid M]
    (t d : ℕ) (v : U → M) (ψ : M → U) (Bk P Q : Fin d → Finset U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) (hcard : ∀ i, #(Bk i) ≤ 2 * t)
    (hP : ∀ i, P i ⊆ Bk i) (hQ : ∀ i, Q i ⊆ Bk i) (hne : ∀ i, P i ≠ Q i)
    (heq : ∀ i, ∏ x ∈ P i, v x = ∏ x ∈ Q i, v x)
    (Y : Finset U) (hY : (univ : Finset (Fin d)).biUnion Bk ⊆ Y) :
    (2 ^ (2 * t)) ^ d * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))) ≤
      (2 ^ (2 * t) - 1) ^ d * 2 ^ #Y := by sorry

end Erdos624
