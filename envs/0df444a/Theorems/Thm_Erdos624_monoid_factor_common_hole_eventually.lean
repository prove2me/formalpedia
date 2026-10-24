-- Prove2me | Theorems.Thm_Erdos624_monoid_factor_common_hole_eventually
-- name    : Erdos624.monoid_factor_common_hole_eventually
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-24T03:33:39.337489+00:00
-- url     : https://prove2.me/theorems/4d586b30-4003-4670-b2ec-51e1ac274593
-- title:
--   Polynomial-size commutative aggregates cannot be half of a covering pair (Erdős 624)
-- statement:
--   **Theorem.** Fix $a\ge0$. There is $k_0$ such that for all $k\ge k_0$ the following holds. Let $|U|=n=2^k$, let $M$ be any finite commutative monoid with $|M|\le n^a$, and let $v:U\to M$, $\psi:M\to U$, $g:\mathcal P(U)\to U$ be arbitrary. Put $h(A)=\psi\bigl(\prod_{x\in A}v(x)\bigr)$. Then there are a $k$-set $Y\subseteq U$ and a point $u\in U$ missed by both $h$ and $g$ on all subsets of $Y$.
--
--   This covers, for example, any fixed number of sums in $\mathbb F_2^k$, $\mathbb F_{2^k}$ or $\mathbb Z/2^k\mathbb Z$, products in a ring of size $n$, mixtures of these, and boundedly many elementary symmetric functions, each followed by arbitrary postprocessing. Consequently, a pair of maps covering every $k$-set for all large $k$ (which would be needed to refute the two-map common-hole route to Erdős Problem 624) cannot have either map of this polynomial-state commutative form. Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ ($|X|=n$) satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it would suffice to show that, for large $k$, any two maps $\mathcal P(U)\to U$ with $|U|=2^k$ have a *common hole*: a $k$-set $Y$ and a point $u$ missed by both maps on $\mathcal P(Y)$.  These results do not settle Problem 624.
--
--   **Formalization Note.** $U$ and $M$ range over arbitrary finite types in `Type`.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); derived from GPT 6.1 Sol's analysis (sixth report, Oct 2026), relayed by Ethan Cheung; Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026)

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset

namespace Erdos624

theorem monoid_factor_common_hole_eventually (a : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ (U M : Type) [Fintype U] [DecidableEq U] [CommMonoid M] [Fintype M],
      Fintype.card U = 2 ^ k → Fintype.card M ≤ (2 ^ k) ^ a →
      ∀ (v : U → M) (ψ : M → U) (g : Finset U → U),
        ∃ Y : Finset U, #Y = k ∧ ∃ u : U,
          u ∉ Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) ∧ u ∉ Y.powerset.image g := by sorry

end Erdos624
