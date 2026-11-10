-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_dynamic_cut_interface
-- name    : DecrAlmostLinearSSSP.Decremental.dynamic_cut_interface
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:53:28.794872+00:00
-- url     : https://prove2.me/theorems/b9dc23be-5d52-4b7a-9ea7-3bdd12517c67
-- title:
--   Lemma 3.2 — Dynamic minimum-ratio cut interface
-- statement:
--   Fix a polynomial numerical-range exponent. There exist one deterministic finite RAM implementation, an absolute constant $C>0$ and positive functions $K,h,\Gamma,a$ of graph-size bound $m$, chosen before the graph and operation stream. Each function is subpolynomial in $m$, and
--
--   $$32\le K(m)\le2^{C(\log\max(2,m))^{5/6}\max(1,\log\log\max(2,m))}.$$
--
--   For every connected physical multigraph of size at most $m$, with positive capacities and zero-sum supplied demand of the fixed polynomial numerical range, and every threshold $\xi>0$, the implementation supports edge insertion and deletion, paired demand changes, ratio tuples, implicit-potential queries and toggling the latest cut. It starts with $y=0$. When demand is nonzero, a tuple satisfies $G<0$, $U>0$, $G=\gamma(C)$, $\operatorname{cut}_u(C)\le U$ and $G/U\le r^*/K$, where $r^*=\min_{\|x\|_u>0}\gamma\cdot x/\|x\|_u$. A toggle with $0\le\tau\le1/U$ adds $\tau1_C$ to $y$ and reports every threshold-crossing edge since insertion or its most recent report.
--
--   Over every legal finite prefix with $L$ operations, $T$ toggles and $R$ emitted reports,
--
--   $$R\le\Gamma(m)T/\xi,\qquad\operatorname{work}\le Cma(m)+h(m)(L+R).$$
--
--   All operations terminate with these guarantees and actual instruction costs, including constant request marshalling. The statement supplies the physical cut implementation needed by the distance algorithm, rather than an assumed free oracle.
--
--   Differences from the source:
--   - reading: the interface assumes polynomially bounded numerical inputs, with magnitude bound U₀ → an arbitrary fixed exponent bounds capacities above and below and demand magnitudes, with implementation constants uniform for that exponent; reason: p.16 explicitly checks these required polynomial ranges; no bound on the eventual full-goal W is imposed
--   - encoding: an implicit cut of minimum-ratio quality and subpolynomial operation and report factors → a finite RAM implementation with semantic views, reusable slots and universal direction inequalities; sizes are saturated by max(2,m) and quality can be padded to K≥32; reason: queries and updates remain actual charged instructions; the direction form equals the minimum form on finite connected inputs and saturation changes only finitely many sizes
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 9, Lemma 3.2, equation (3.12), preamble and footnote 2; p. 16, numerical ranges; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_CutProtocol

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- Lemma 3.2: all implementation properties, including actual operation costs, are
conclusions. Polynomial numerical ranges have an exponent fixed before graph instances. -/
theorem dynamic_cut_interface :
    ∀ exponent : ℕ, ∃ (impl : CutImplementation) (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → ImplementsCut impl m exponent (K m) (h m) (Γ m)
        (C * m * a m) ξ := by sorry

end DecrAlmostLinearSSSP.Decremental
