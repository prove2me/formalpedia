-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_dynamic_cut_interface
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_cut_interface
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T04:14:43.524193+00:00
-- url     : https://prove2.me/theorems/7478a32e-d2b3-400b-a09b-2d573243d298
-- title:
--   Lemma 3.2 — Implemented dynamic cuts on nonempty vertex domains
-- statement:
--   Fix a natural exponent $d$ bounding the numerical range. There is one finite deterministic scalar arithmetic-RAM program, chosen before the graph size, detector threshold and update stream, together with a positive constant $C$ and positive subpolynomial functions $K,h,\Gamma,a$.
--
--   For each size bound $m$, the quality satisfies
--
--   $$32\le K(m)\le 2^{C(\log\max\{2,m\})^{5/6}\max\{1,\log\log\max\{2,m\}\}}.$$
--
--   The program initializes on every nonempty physical undirected multigraph with $n,k\le m$, positive active capacities in $[\max(2,m)^{-d},\max(2,m)^d]$, total demand zero and vertex demands bounded in absolute value by $\max(2,m)^d$. The zero-seminorm directions are exactly the constant vectors. A supplied positive capacity bound covers the initial active capacities and is at most $\max(2,m)^d$.
--
--   The program terminates after initialization and every legal insertion, deletion, paired demand change, ratio request, cut toggle or potential query. It maintains the actual physical updates and an implicit potential initially zero. For nonzero demand, a returned cut $S$ and numbers $G<0<U$ satisfy
--
--   $$G=\sum_{v\in S}\gamma_v,\qquad \operatorname{cap}(S)\le U,\qquad \frac GU\le\frac{\gamma\cdot x}{K(m)\,\|x\|_u}\quad(\|x\|_u>0).$$
--
--   A legal toggle adds $\tau\mathbf 1_S$ to the maintained potential, where $0\le\tau\le1/U$. For any threshold $\xi>0$, every active edge whose capacity-weighted endpoint difference changes by at least $\xi$ since insertion or its last report is explicitly reported. Baselines update exactly on reported identifiers. Queries return the maintained potential at the requested vertex.
--
--   If $T$ toggles and $q$ total operations have completed and $R$ identifiers have been emitted, then
--
--   $$R\le\frac{\Gamma(m)T}{\xi},\qquad \operatorname{work}\le Cma(m)+h(m)(q+R).$$
--
--   Initialization, all operation bodies and all output writes are actual finite RAM executions; no accurate cut oracle or successful-execution certificate is an input. This is the implemented cut interface required by Lemma 3.2 and the repair algorithm in §3.2.
--
--   **Formalization Note** The semantic view is required only when $n>0$. This preserves every admitted graph instance while avoiding the impossible unrestricted request for a graph with $n=0$ and $k=1$. All original physical, toggle, ratio, baseline, detector and work guarantees are retained.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2 and §3.2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. The original admitted graph domain is nonempty; the semantic-view domain is restricted accordingly.

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

theorem dynamic_cut_interface :
    ∀ exponent : ℕ, ∃ (impl : Implementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → Implements impl m exponent (K m) (h m) (Γ m)
        (C * m * a m) ξ := by sorry

end DecrAlmostLinearSSSP.Decremental.NonemptyCut
