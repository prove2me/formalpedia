-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_theorem_2
-- name    : EdgeSublinearMWIS.Main.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:09.353567+00:00
-- url     : https://prove2.me/theorems/95bc831e-e24d-44bc-9a7c-df29230e2bc1
-- title:
--   Theorem 2 — deterministic QPTAS for maximum weight independent set
-- statement:
--   Let $\mathcal C$ be any hereditary class of finite simple undirected graphs with strongly edge-sublinear separators. There is one finite deterministic program for the entire class, with class-uniform $K>0$, positive integer $d$ and a universal positive polynomial exponent $q$. For every graph $G\in\mathcal C$ with $n$ vertices, arbitrary rational weights $w$ and rational $0<\varepsilon<1$, it returns an independent set $I$ satisfying
--   $$w(I)\ge(1-\varepsilon)\alpha_w(G),\qquad T\le K\exp\!\left(K(\varepsilon^{-1}\log_2\max\{2,n\})^d\right)+K(\ell+1)^q.$$
--   Here $\alpha_w$ maximizes over all independent subsets including the empty set, and $\ell$ is the total binary length of the weight and accuracy encodings, including signs and prefixes. Every positive-denominator representation is accepted, including unreduced fractions. The finite program precedes every input and its time is the first actual halting step on a local binary Turing machine. It receives only adjacency, weights and accuracy. No class-membership oracle, separator, separator-finding algorithm, optimum or input-dependent advice is supplied.
--
--   This is the full weighted source target. Negative weights, empty graphs, singleton graphs and all-nonpositive vectors remain in the domain. The additive polynomial encoding work and the class-uniform quasipolynomial term are both preserved.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: rational weights and accuracy with binary length ell → arbitrary signed numerator and positive-denominator encodings, with sign and self-delimiting prefixes counted in ell; reason: every rational value and every such representation is included; normalization must be charged
--   - encoding: exp((epsilon inverse log n)^(O_C(1))) plus ell^(O(1)) → uniform K,d before all inputs, universal q before the class, and log_2(max(2,n)); reason: positive constants and padding express the source asymptotics; max handles its direct empty and singleton cases
--   - encoding: a deterministic algorithm without supplied separators → one ordinary finite bit machine, empty catalyst and first actual halting time; reason: no correctness, resource bound, optimizer or per-instance advice is assumed in the computational model
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 2 and explanatory paragraph, p.2; repeated proof p.20, p.2 (PDF p.2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- Theorem 2, including its p.2 explanatory paragraph: arbitrary signed rational
weights, a single finite deterministic program, additive bit preprocessing, no oracle. -/
theorem theorem_2 :
    ∃ q : ℕ, 0 < q ∧ ∀ C : GraphClass, StronglyEdgeSublinear C →
      ∃ (M : CatalyticMatching.General.Machine) (K : ℝ) (d : ℕ), 0 < K ∧ 0 < d ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode)
          (ε : RationalCode), C n G → 0 < ε.value → ε.value < 1 →
          ∃ (I : Finset (Fin n)) (s : ℕ),
            BitHalts M (weightedInput G w ε) (mask I) s ∧
            G.IsIndepSet (I : Set (Fin n)) ∧
            (1 - (ε.value : ℝ)) * weightedAlpha G (fun v => (w v).value) ≤
              ∑ v ∈ I, ((w v).value : ℝ) ∧
            (s : ℝ) ≤ K * Real.exp
              (K * (((ε.value : ℝ))⁻¹ * logTwo (max 2 n)) ^ d) +
                K * ((rationalData w ε).length + 1 : ℝ) ^ q := by sorry

end EdgeSublinearMWIS.Main
