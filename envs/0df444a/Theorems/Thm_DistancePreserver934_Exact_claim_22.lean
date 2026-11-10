-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_claim_22
-- name    : DistancePreserver934.Exact.claim_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:56.282836+00:00
-- url     : https://prove2.me/theorems/83fbd29c-9982-4fba-8c1a-6c6945d29bc2
-- title:
--   Claim 22 — residual demand sets of at most half the size
-- statement:
--   Let $G$ be a graph on $n$ vertices and $p$ an integer with $n^{7/10}<p\le n$ (the inductive step of §6.2). Let $C_{CE}$ satisfy Equation (31): every minimal distance preserver $J$ of every graph on these $n$ vertices with demand set $T$ has $|E(J)|\le C_{CE}(n+n^{1/2}|T|)$. Let $C\ge2^{13/9}C_{CE}$, and assume the **induction hypothesis**: for every graph on these vertices and every demand set $T$ with $n^{1/4}\le|T|\le p-1$, every minimal distance preserver $J$ satisfies $|E(J)|\le C\,n^{8/9}|T|^{4/9}$. Then every minimal distance preserver $J$ of $(G,R)$, $R$ a demand set with $|R|\le p/2$, satisfies
--   $$|E(J)|\le C\,n^{8/9}(p/2)^{4/9}.\tag{32}$$
--
--   Residual sets below the cutoff, $|R|<n^{1/4}$ (including $R=\emptyset$), are included. The claim is the upper bound (42) that closes the induction.
--
--   Differences from the source:
--   - encoding: p = |P| for the demand set P of the inductive step → p a natural number in the range n^{7/10} < p ≤ n; reason: P enters Claim 22 only through its size p
--   - encoding: the induction hypothesis and Equation (31) for all n-vertex graphs → for all graphs on the given n-element vertex type; reason: all quantities are invariant under graph isomorphism
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Claim 22 (with Equation (31) and the induction of §6.2), printed p. 22 (PDF p. 23)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers

namespace DistancePreserver934.Exact

open Classical

/-- Claim 22, printed p.22 / PDF p.23.  Let `G` be a graph on `n` vertices and
`n^{7/10} < p ≤ n`.  Let `C_CE` satisfy Equation (31) for every graph on these vertices, let
`C ≥ 2^{13/9} C_CE`, and assume the induction hypothesis: Equation (26) with constant `C` for
every graph on these vertices and every demand set of size `t` with `n^{1/4} ≤ t ≤ p − 1`.
Then every minimal distance preserver `J` of `(G, R)` with `|R| ≤ p/2` satisfies
`|E(J)| ≤ C n^{8/9} (p/2)^{4/9}` (Equation (32)). -/
theorem claim_22 {V : Type} [Fintype V] (G : SimpleGraph V) (p : ℕ) (C C_CE : ℝ)
    (hp₁ : (Fintype.card V : ℝ) ^ ((7 : ℝ) / 10) < (p : ℝ))
    (hp₂ : (p : ℝ) ≤ (Fintype.card V : ℝ))
    (hCE : ∀ (G' J : SimpleGraph V) (T : Finset (Sym2 V)),
      IsDemandSet G' T → IsMinimalPreserver G' J T →
      (numEdges J : ℝ) ≤ C_CE * ((Fintype.card V : ℝ) +
        (Fintype.card V : ℝ) ^ ((1 : ℝ) / 2) * (T.card : ℝ)))
    (hC : (2 : ℝ) ^ ((13 : ℝ) / 9) * C_CE ≤ C)
    (IH : ∀ (G' J : SimpleGraph V) (T : Finset (Sym2 V)),
      IsDemandSet G' T → (Fintype.card V : ℝ) ^ ((1 : ℝ) / 4) ≤ (T.card : ℝ) → T.card < p →
      IsMinimalPreserver G' J T →
      (numEdges J : ℝ) ≤ C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * (T.card : ℝ) ^ ((4 : ℝ) / 9))
    (R : Finset (Sym2 V)) (J : SimpleGraph V)
    (hR : IsDemandSet G R) (hRp : (R.card : ℝ) ≤ (p : ℝ) / 2) (hJ : IsMinimalPreserver G J R) :
    (numEdges J : ℝ) ≤
      C * (Fintype.card V : ℝ) ^ ((8 : ℝ) / 9) * ((p : ℝ) / 2) ^ ((4 : ℝ) / 9) := by sorry

end DistancePreserver934.Exact
