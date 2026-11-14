-- Prove2me | Theorems.Thm_BCFGJPSSV26_facilityLocation_lmp
-- name    : BCFGJPSSV26.facilityLocation_lmp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:44:58.14632+00:00
-- url     : https://prove2.me/theorems/079656d4-979f-475f-9dab-d2467fa2cbf4
-- title:
--   Theorem 1.4 (Part I) — a polynomial-time $1.9499$-LMP approximation for facility location
-- statement:
--   This is Theorem 1.4 of Part I (arXiv:2610.18144; Theorem 4.3 in the full version): there is a polynomial-time $1.9499$-LMP (Lagrangian multiplier preserving) approximation algorithm for uncapacitated facility location with a uniform opening cost.
--
--   **Model.** An instance $I$ consists of $n$ clients, $m$ facilities and rational distances between the $n+m$ points (and a number $k$, which plays no role here). It is *valid* if $m\ge1$, $k\ge1$ and the distances form a pseudometric (nonnegative, zero on the diagonal, symmetric, with the triangle inequality). For a nonempty set $S$ of facilities, $\mathrm{cost}(S)=\sum_{j}\min_{i\in S}d(j,i)$, the sum being over the clients $j$. With a uniform opening cost $f$, the optimum of facility location is
--
--   $$\mathrm{OPT}_f=\min_{S'\ne\emptyset}\big(\mathrm{cost}(S')+f\,|S'|\big),$$
--
--   the minimum being over the nonempty sets $S'$ of facilities.
--
--   **Statement.** There is a deterministic algorithm $A$ that takes an instance $I$ and a rational number $f$ and returns a list of natural numbers, such that:
--
--   1. **Running time.** $A$ is computable in polynomial time: a deterministic multitape Turing machine computes it within time and space polynomially bounded in the length of the encoded input (the instance as $n$, $m$, $k$ in binary with its table of distances, and $f$ as a rational number in binary).
--   2. **Guarantee.** For every valid instance $I$ with at least one client ($n\ge1$) and every rational opening cost $f\ge0$, the output $S=A(I,f)$ is a nonempty list of distinct facilities of $I$, and
--
--   $$\mathrm{cost}(S)\ \le\ 1.9499\,\big(\mathrm{OPT}_f-f\,|S|\big).$$
--
--   This inequality is the LMP guarantee of Part I, Definition 2.1, with factor $1.9499$; $|S|$ is the number of facilities in the output.
--
--   **Role.** This is the facility-location result of the paper. It is proved with the greedy algorithm and the robust LMP guarantee developed for the pseudo-approximation (Theorem 1.2): the greedy algorithm is run once, at one opening cost, on a rescaled instance, and the output is the better of this run and the trivial solution (the nearest facility of every client).
--
--   **Formalization Note** The paper's Theorem 4.3 says that Algorithm 1 with the bid $[\alpha-1.224\,d]^+$ and the opening cost $1.9499f$ is such an algorithm; the formal statement asserts that some algorithm has the guarantee. Instances without clients are excluded: there the paper's optimum opens no facility and is $0$, while here outputs are nonempty and $\mathrm{OPT}_f$ ranges over nonempty sets. Distances and $f$ are rational, and a point that is both a client and a facility is represented by two points at distance $0$.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 1.4 (Theorem 4.3 in full). Lean source: `BCFGJPSSV26.facilityLocation_lmp`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Solution.lean#L73-L84

module

public import Definitions.Def_BCFGJPSSV26_Model
import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import Definitions.Def_BCFGJPSSV26_FL_Main

set_option maxSynthPendingDepth 3

public section

namespace BCFGJPSSV26

open Encoding

theorem facilityLocation_lmp :
    ∃ A : Instance × ℚ → List ℕ,
      Turing.MultiTapeTM.ComputableInPolyTime A (encPair encInstance encRat) encCenters ∧
      ∀ I : Instance, I.Valid → 0 < I.n → ∀ f : ℚ, 0 ≤ f →
        I.IsCenterList (A (I, f)) ∧
        I.cost (I.centers (A (I, f))) ≤
          1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (A (I, f)).length) := by sorry

end BCFGJPSSV26
end
