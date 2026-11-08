-- Prove2me | Theorems.Thm_BC1992_lemma_3_1_tm_simulation_in_bc
-- name    : BC1992.lemma_3_1_tm_simulation_in_bc
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-08T00:37:10.499854+00:00
-- url     : https://prove2.me/theorems/94f000cd-30c1-4b91-bd0e-bb017ed430cf
-- title:
--   Lemma 3.1: Simulation of Polynomial-Time Multi-Tape Turing Machines in Bellantoni-Cook Safe Recursion
-- statement:
--   Establishes Lemma 3.1 of Bellantoni and Cook (1992) for every deterministic multi-tape Turing machine $M : \mathsf{TM}$:
--
--   1. $|(\mathsf{polyWord}\;q).\mathsf{eval}\;[x]\;[]| = q(|x|)$ for every syntactic polynomial $q : \mathsf{Poly}$.
--   2. $(\mathsf{initCfgBC}\;M).\mathsf{eval}\;[W]\;[x] = \mathsf{encCfg}\;M\;|W|\;(M.\mathsf{init}\;x)$.
--   3. If $M.\mathsf{TapeBounded}\;|W|\;c$, then $(\mathsf{stepCfgBC}\;M).\mathsf{eval}\;[W]\;[\mathsf{encCfg}\;M\;|W|\;c] = \mathsf{encCfg}\;M\;|W|\;(M.\mathsf{stepOrSelf}\;c)$.
--   4. If $|x| + |T| \le |W|$, then $(\mathsf{runCfgBC}\;M).\mathsf{eval}\;[T, W]\;[\mathsf{encCfg}\;M\;|W|\;(M.\mathsf{init}\;x)] = \mathsf{encCfg}\;M\;|W|\;(M.\mathsf{run}\;|T|\;(M.\mathsf{init}\;x))$.
--   5. If $|(c.\mathsf{tapes}\;0).\mathsf{right}| < |W|$, then $(\mathsf{outputCfgBC}\;M).\mathsf{eval}\;[W]\;[\mathsf{encCfg}\;M\;|W|\;c] = M.\mathsf{output}\;c$.
--   6. Consequently, for every polynomial clock $p : \mathsf{Poly}$ and input $x : \mathsf{Word}$, $(\mathsf{simTM}\;M\;p).\mathsf{eval}\;[x]\;[] = M.\mathsf{output}\bigl(M.\mathsf{run}\;(p(|x|))\;(M.\mathsf{init}\;x)\bigr)$.
-- source:
--   Stephen Bellantoni and Stephen Cook, 'A new recursion-theoretic characterization of the polytime functions', Computational Complexity 2 (1992), pp. 97-110 (doi:10.1007/BF01201998). Section 3, Lemma 3.1, pp. 102-105.

import Definitions.Def_BC1992_Syntax
import Definitions.Def_BC1992_Machines
import Definitions.Def_BC1992_Simulation

namespace BC1992

/-- **Lemma 3.1 (Bellantoni & Cook 1992 — Multi-Tape Turing Machine Simulation in `BC`)**:
    For every deterministic multi-tape Turing machine `M : TM`:
    1. (`length_eval_polyWord`) `((polyWord q).eval [x] []).length = q.eval x.length`.
    2. (`eval_initCfgBC`) `(initCfgBC M).eval [W] [x] = encCfg M W.length (M.init x)`.
    3. (`eval_stepCfgBC`) If `M.TapeBounded W.length c`, then
       `(stepCfgBC M).eval [W] [encCfg M W.length c] = encCfg M W.length (M.stepOrSelf c)`.
    4. (`eval_runCfgBC`) If `x.length + T.length ≤ W.length`, then
       `(runCfgBC M).eval [T, W] [encCfg M W.length (M.init x)] = encCfg M W.length (M.run T.length (M.init x))`.
    5. (`eval_outputCfgBC`) If `(c.tapes ⟨0, M.hk⟩).right.length < W.length`, then
       `(outputCfgBC M).eval [W] [encCfg M W.length c] = M.output c`.
    6. (`eval_simTM`) For every polynomial clock `p : Poly` and input word `x : Word`,
       `(simTM M p).eval [x] [] = M.output (M.run (p.eval x.length) (M.init x))`. -/
theorem lemma_3_1_tm_simulation_in_bc :
    (∀ (q : Poly) (x : Word),
      ((polyWord q).eval [x] []).length = q.eval x.length) ∧
    (∀ (M : TM) (W x : Word),
      (initCfgBC M).eval [W] [x] = encCfg M W.length (M.init x)) ∧
    (∀ (M : TM) (W : Word) {c : Cfg M.k M.Q M.G},
      M.TapeBounded W.length c →
      (stepCfgBC M).eval [W] [encCfg M W.length c] = encCfg M W.length (M.stepOrSelf c)) ∧
    (∀ (M : TM) (T W x : Word),
      x.length + T.length ≤ W.length →
      (runCfgBC M).eval [T, W] [encCfg M W.length (M.init x)] =
        encCfg M W.length (M.run T.length (M.init x))) ∧
    (∀ (M : TM) (W : Word) {c : Cfg M.k M.Q M.G},
      (c.tapes ⟨0, M.hk⟩).right.length < W.length →
      (outputCfgBC M).eval [W] [encCfg M W.length c] = M.output c) ∧
    (∀ (M : TM) (p : Poly) (x : Word),
      (simTM M p).eval [x] [] = M.output (M.run (p.eval x.length) (M.init x))) := by
  sorry

end BC1992
