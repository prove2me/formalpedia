-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_33
-- name    : APrioriTSP.Sampling.lemma_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:34.351278+00:00
-- url     : https://prove2.me/theorems/c351ff39-0f0a-4e69-abf3-fe3e44283344
-- title:
--   Lemma 33, p. 33 — lowering activation probabilities (depot fixed at 1) does not increase the cost of an optimum a priori tour
-- statement:
--   Let $(V, c, p)$ be an instance of the a priori TSP with depot $d$, and let $T^*$ be an optimum a priori tour for it. Let $p' : V \to (0,1]$ with $p'(v) \le p(v)$ for all $v \in V$ and $p'(d) = p(d) = 1$. Then
--   $$\mathrm{OPT}(V, c, p') \le \mathbb E_{A\sim p'}[c(T^*[A])] \le \mathbb E_{A\sim p}[c(T^*[A])] = \mathrm{OPT}(V, c, p).$$
--
--   The lemma gives part (i) of the reduction in the proof of Lemma 9: the normalized instance built from copies of customers has an optimum no larger than the original one.
--
--   **Formalization Note** "Optimum a priori tour" is the hypothesis that $T^*$ is a tour whose a priori cost under $p$ is at most that of every tour.
--
--   Differences from the source: none.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 33, Lemma 33

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

/-- Lemma 33 (p. 33): lowering the activation probabilities (keeping the depot at `1`) does not
increase the a priori cost of an optimum tour. -/
theorem lemma_33 {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (p p' : V → ℝ) (d : V) (hI : IsDepotInstance c p d)
    (hp' : ∀ v, 0 < p' v ∧ p' v ≤ 1) (hle : ∀ v, p' v ≤ p v) (hd : p' d = 1)
    (T : List V) (hT : IsTour T)
    (hopt : ∀ T' : List V, IsTour T' → aPrioriCost c p T ≤ aPrioriCost c p T') :
    aPrioriOpt c p' ≤ aPrioriCost c p' T ∧ aPrioriCost c p' T ≤ aPrioriCost c p T ∧
      aPrioriCost c p T = aPrioriOpt c p := by sorry

end APrioriTSP.Sampling
