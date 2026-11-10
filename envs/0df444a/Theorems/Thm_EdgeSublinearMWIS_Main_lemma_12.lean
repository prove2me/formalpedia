-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_12
-- name    : EdgeSublinearMWIS.Main.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:43:08.635776+00:00
-- url     : https://prove2.me/theorems/918a0145-24f7-4abe-8cb2-5361589984fc
-- title:
--   Lemma 12 — deterministic conditioning of the relaxation
-- statement:
--   For a graph $G$ on $n$ vertices, integers $1\le k\le n$, $r\ge1$, $p\ge1$, and a rational point $y\in R_r(G,k)$, assume $r\ge2p\log_2n$. A deterministic program finds the first set $A$ passing the source's exact rational conditioning test, with $|A|\le r$ and $y_A>0$. Its costs $x_v=y_{A\cup\{v\}}/y_A$ satisfy
--   $$x\in[0,1]^{V(G)},\qquad \sum_vx_v=k,\qquad e_G(x)\le k^2/p.$$
--   Runtime is polynomial in $r$ and the encoding lengths of $y$ and $p$. The point need only satisfy all rows of (13); it is not assumed to lie in the indicator hull or to be a true independent-set distribution. This produces the auxiliary costs for the light-separator routine.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: a deterministic polynomial-time algorithm on rational inputs → one finite program, serialized rational inputs and actual halting-step bounds; reason: binary conventions fix a computational model without restricting rational values
--   - encoding: find a suitable set by exhaustive testing → return the first passing set in a fixed subset enumeration; reason: the source algorithm permits any enumeration and no entropy computation is introduced
--   - encoding: coordinates only up to r+2 → total arrays whose other entries are ignored and not serialized; reason: this is a finite-coordinate adapter, not an added feasibility hypothesis
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 12, p.13 (PDF p.13), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_RoundOrCut

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

theorem lemma_12 :
    ∃ (M : Program) (time : Polynomial ℕ),
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (r k p : ℕ) (y : Finset (Fin n) → ℚ),
        1 ≤ k → k ≤ n → 1 ≤ r → 1 ≤ p →
        Relaxation G Finset.univ r k (fun A => (y A : ℝ)) →
        2 * p * logTwo n ≤ (r : ℝ) →
        ∃ (A : Finset (Fin n)) (t : ℕ),
          conditioningChoice G Finset.univ r k p y = some A ∧
          A.card ≤ r ∧ 0 < y A ∧
          (∀ v, 0 ≤ queryCosts y A v ∧ queryCosts y A v ≤ 1) ∧
          (∑ v, queryCosts y A v) = (k : ℚ) ∧
          edgeEnergy G (fun v => (queryCosts y A v : ℝ)) ≤ (k : ℝ) ^ 2 / p ∧
          Runs M (graphBits G ++ encodeNat r ++ encodeNat k ++ encodeNat p ++
            encodePoint Finset.univ r y) (mask A) t ∧
          t ≤ time.eval (r + (encodePoint Finset.univ r y).length +
            (encodeNat p).length + 1) := by sorry

end EdgeSublinearMWIS.Main
