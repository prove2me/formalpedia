-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_general_domain_adapter
-- name    : DecrAlmostLinearSSSP.Decremental.general_domain_adapter
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T00:47:30.689213+00:00
-- url     : https://prove2.me/theorems/e3f20f67-1f7d-4281-a978-cceae0fa7a8f
-- title:
--   General-domain adapter for a charged polynomial-weight decremental solver
-- statement:
--   Suppose one deterministic scalar arithmetic-RAM program handles all valid inputs with at least two vertices, integer weights bounded by the square of the size bound, and accuracy strictly between the reciprocal size bound and one. Assume that it explicitly maintains simultaneous approximate source distances and exact unreachability, terminates after every legal deletion prefix, has a uniform constant query bound, and has total charged maintenance work
--
--   $$\operatorname{work}\le Cma(m)\epsilon^{-1},$$
--
--   where $C>0$ and $a$ is positive and subpolynomial. Then there is one deterministic scalar arithmetic-RAM program for the full input domain, including singleton graphs, arbitrarily small positive real accuracy, and arbitrary positive integer weight bound $W$. It has a uniform constant query bound and satisfies
--
--   $$d_G(s,v)\le D(v)\le(1+\epsilon)d_G(s,v)\quad(v\in V),$$
--   $$\operatorname{work}\le C'ma'(m)\epsilon^{-1}\max(1,\log_2W),$$
--   $$\frac{\log a'(m)}{\log\max(2,m)}\longrightarrow0.$$
--
--   The new program and constants may depend on the supplied polynomial-weight solver but are chosen before every full-domain graph and deletion stream. This is the general-domain reduction on p.4 and its footnote, expressed as a reusable implication between charged online-program guarantees. It retains initialization, exact infinity, stored-array queries and all adapter work.
--
--   **Formalization Note** The exponent two suffices for the mission's rounded instances: internal accuracy is $\epsilon/16$, size is padded to $64m$, and weights are rounded with $\Delta_L=\epsilon L/(128n)$. These explicit wrapper choices are from the mission definitions; the paper's reduction is unnumbered. The small-accuracy and singleton branches remain implementation obligations, and no successful-run or output-accuracy certificate is supplied as input.
-- source:
--   Cui, Li, Miao, Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912 (October 2026), p.4, unnumbered general-domain reduction and footnote 1; p.3, Theorem 1.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf . The concrete rounding/padding parameters are those fixed by the mission adapter definitions, not a separately numbered source lemma.

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Adapters

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

theorem general_domain_adapter
    (p : Program) (C : ℝ) (a : ℕ → ℝ) (queryBound : ℕ)
    (hC : 0 < C) (hquery : 0 < queryBound) (ha : Subpolynomial a)
    (hpoly : ∀ i : Input, i.Valid → 2 ≤ i.n → i.W ≤ i.size ^ 2 →
      1 / (i.size : ℝ) < i.accuracy → i.accuracy < 1 →
      Maintains p C a queryBound false i) :
    ∃ (p' : Program) (C' : ℝ) (a' : ℕ → ℝ) (queryBound' : ℕ),
      0 < C' ∧ 0 < queryBound' ∧ Subpolynomial a' ∧
      ∀ i : Input, i.Valid → Maintains p' C' a' queryBound' true i := by sorry

end DecrAlmostLinearSSSP.Decremental
