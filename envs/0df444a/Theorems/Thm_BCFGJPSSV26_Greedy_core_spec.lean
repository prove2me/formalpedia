-- Prove2me | Theorems.Thm_BCFGJPSSV26_Greedy_core_spec
-- name    : BCFGJPSSV26.Greedy.core_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:13.612965+00:00
-- url     : https://prove2.me/theorems/15162b35-7617-4162-86f8-eebb0fc03176
-- title:
--   The core theorem: Theorem 5.16 (Part I) on inputs with distances in $[1,M]$
-- statement:
--   This is Theorem 5.16 of Part I on a core input, that is, when all client–facility distances lie in $[1,M]$: the core of the log-adaptive greedy algorithm opens at most $k+6R$ facilities, of cost at most $\rho+10\delta$ times the cost of any $k$ facilities.
--
--   **Setting.** Fix rational constants $\delta,\varepsilon_g,\varepsilon'$ with $0<\delta\le\tfrac1{100}$, $\varepsilon_g=\tfrac{\delta}{10}$ and $0<\varepsilon'\le1$. A core input is $(n,m,k,\text{table})$, where the table holds the client–facility distances $d(j,i)$ of a pseudometric space with rational distances on $n$ clients and $m$ facilities, and
--   $$n\ge2,\qquad 1\le k<\min(n,m),\qquad 1\le d(j,i)\le M:=\frac{8n^2}{\varepsilon'}+1 .$$
--   Let $R=\lceil1/\varepsilon_g^2\rceil\cdot\lceil\log_2\lceil5nM\rceil\rceil+1$, $\gamma=\tfrac{153}{125}$ and $\rho=2-(\gamma-1)^2=1.949824$. For a nonempty set or list $T$ of facilities, $\mathrm{cost}(T)=\sum_j\min_{i\in T}d(j,i)$.
--
--   **The core** is deterministic and uses exact rational arithmetic. For an opening cost $\hat f$ it runs the log-adaptive greedy algorithm of Section 5 and Appendix D of Part I with the bid $\beta(\alpha,d)=[\alpha-\gamma d]^+$: $2R$ sequences, alternately of type 1 and type 2, at times $(1+\varepsilon_g^2)^r$, each built by opening the first facility that passes an exact openability test, as long as there is one. By bisection on a grid of $[\delta,4nM]$ of step at most $\delta^2/(100n^2)$ it finds a solution with at most $k$ regular facilities at $\hat f=\delta$, or one with exactly $k$, or two solutions at adjacent grid points with more and fewer than $k$. In the last case it merges them, one phase per sequence, using free copies of facilities at an offset. The output lists the facilities of the final solution, free copies replaced by their originals, without repetitions.
--
--   **Statement.** The output $S$ of the core, a list of facility indices, satisfies:
--
--   1. $S$ is nonempty, has no repetitions, and every entry is less than $m$;
--   2. $|S|\le k+6R$;
--   3. for every nonempty set $O$ of at most $k$ facilities,
--   $$\mathrm{cost}(S)\le(\rho+10\delta)\,\mathrm{cost}(O).$$
--
--   The main algorithm of Theorem 1.2 of Part I runs the core on a scaled copy of the instance for every guess of the largest distance of a client to the optimum, and keeps the cheapest output. The statement rests on the correctness of the merge and on the robust LMP guarantee (Theorem D.7 of Part I).
--
--   **Formalization Note** The cost of $S$ is computed exactly from the table. The table is read with the default value $0$ outside its range, and the values read are assumed nonnegative.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 5.16. Lean source: `BCFGJPSSV26.Greedy.core_spec`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/Core.lean#L156-L216

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Merge
public import Definitions.Def_BCFGJPSSV26_Greedy_LMP
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDups
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Ctx

variable {C : Ctx} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

end Ctx

set_option maxHeartbeats 1000000 in

theorem core_spec {c : Consts} (hc : c.Good) {x : CoreIn} {X : Space x.1 x.2.1}
    (hx : CoreOK c x X) :
    core c x ≠ [] ∧ (core c x).Nodup ∧ (∀ i ∈ core c x, i < x.2.1) ∧
      (core c x).length ≤ x.2.2.1 + 6 * Rof c x.1 ∧
      ∀ O : Finset (Fin x.2.1), O.Nonempty → O.card ≤ x.2.2.1 →
        coreCost x (core c x) ≤ (ρ + 10 * c.δ) * costF X.d O := by sorry

end BCFGJPSSV26.Greedy
end
