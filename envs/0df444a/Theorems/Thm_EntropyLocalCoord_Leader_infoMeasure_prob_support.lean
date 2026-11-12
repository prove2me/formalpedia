-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_infoMeasure_prob_support
-- name    : EntropyLocalCoord.Leader.infoMeasure_prob_support
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:50.173113+00:00
-- url     : https://prove2.me/theorems/6cc012c8-39cd-4f33-82d1-14e735237bac
-- title:
--   §4, p. 11 — $\mu_i=df_{X_i}$ is a probability measure supported on $B(i)$
-- statement:
--   Let $\pi=(X_i,Z_j)$ be a binary coordination profile adapted to the information skeleton $\mathfrak S=(N,K,B)$, and let $i\in N$. Then $\mu_i:=df_{X_i}$ is a probability measure on $K$ with $\operatorname{supp}(\mu_i)\subseteq B(i)$. That is,
--
--   $$\mu_i(\{j\})\ge0\ \ (j\in K),\qquad\sum_{j\in K}\mu_i(\{j\})=1,\qquad\mu_i(\{j\})=0\ \ (j\notin B(i)).$$
--
--   The total mass is $H(X_i)=1$, an unbiased binary variable having one bit of entropy. The support claim is where the independence of the sources enters.
--
--   Differences from the source:
--   - encoding: the players are $N=\{1,\dots,n\}$ and the sources $K=\{1,\dots,k\}$ → the types `Fin n` and `Fin k`, indexed from 0, with $n=0$ admitted by the type; reason: a relabeling; the empty-player instance adds only a trivial case and changes no source instance
--   - encoding: an arbitrary probability space and arbitrary source variables → the sample space and the source value spaces lie in Lean's universe `Type`; reason: the source fixes no universe; every measurable space used in the mathematics is represented
--   - encoding: sources numbered $1,\dots,k$ with $df_X(\{j\})=f_X(j)-f_X(j-1)$ → index $j$ of `Fin k` carries $f_X(j+1)-f_X(j)$; reason: the same fixed ordering of $K$, shifted by one
--   - encoding: $\mu_i$ is a probability measure on $K$ with $\operatorname{supp}(\mu_i)\subseteq B(i)$ → a real vector on `Fin k` that is nonnegative, sums to 1 and vanishes off $B(i)$; reason: on a finite set these say the same thing
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, §4, p. 11, first line (and p. 10, H(X) = 1 for every unbiased binary variable).

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Information

namespace EntropyLocalCoord.Leader

/-- §4, p. 11: for a binary coordination profile, `μ_i := df_{X_i}` is a probability measure on
`K` with `supp(μ_i) ⊆ B(i)`. -/
theorem infoMeasure_prob_support {n k : ℕ} (S : InformationSkeleton n k)
    (π : CoordinationProfile S) (hπ : π.IsBinary) (i : Fin n) :
    (∀ j, 0 ≤ infoMeasure π.P π.Z (π.X i) j) ∧
      ∑ j, infoMeasure π.P π.Z (π.X i) j = 1 ∧
      ∀ j, j ∉ S.B i → infoMeasure π.P π.Z (π.X i) j = 0 := by sorry

end EntropyLocalCoord.Leader
