-- Prove2me | Theorems.Thm_BCFGJPSSV26_FL_sol_eta
-- name    : BCFGJPSSV26.FL.sol_eta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:39:26.128825+00:00
-- url     : https://prove2.me/theorems/5a2bb0d6-28a1-4573-845f-31b5b5f8d7d0
-- title:
--   Valid greedy solutions do not depend on the slack $\eta$ stored in the parameters
-- statement:
--   This is a bookkeeping lemma about the $\eta$-valid solutions of the greedy algorithm of Part I (arXiv:2610.18144; Definitions D.3 and D.6): the notion depends on the slack only through its explicit slack argument, not through the slack stored in the parameters.
--
--   **Setting.** Fix $n$ clients, $m$ facilities and rational client–facility distances $d(j,i)$. The parameters are $P=(\delta,\varepsilon,\eta_P,K,R)$: the paper's $\delta$ and $\varepsilon$, a slack $\eta_P$, the cap $K$ of the distance profiles and the number $R$ of phases. An *atom* is an opened facility, regular or a free copy at some offset. For an opening cost $f\in\mathbb Q$ and a slack $\eta\in\mathbb Q$, a list $H$ of sequences of atoms is an *$\eta$-valid solution*, written $\mathrm{Sol}_P(d,f,\eta,H)$, if:
--
--   1. $H$ consists of exactly $2R$ sequences;
--   2. every sequence is $\eta$-valid: in sequence $p$ (of type 1 if $p$ is even, of type 2 if $p$ is odd, at time $(1+\varepsilon^2)^{\lfloor p/2\rfloor}$) every regular atom is $(\text{type},\eta)$-openable (Part I, Definitions D.1 and D.2) with respect to some set of pairs (facility, offset), with nonnegative offsets, that contains those of all atoms before it, and no facility is $(\text{type},0)$-openable after the sequence;
--   3. every atom is well-formed: regular atoms have offset $0$, and offsets lie in $[0,K]$;
--   4. every client $j$ is inactive at the end: $(1-\delta)\,D_j\le(1+\varepsilon^2)^R$, where $D_j=\min\big(K,\min_{(i,u)}(d(j,i)+u)\big)$ over the atoms (facility $i$, offset $u$) of $H$.
--
--   **Statement.** Let $H$ be an $\eta$-valid solution for the parameters $P$, the distances $d$ and the opening cost $f$. Then for every $\eta'\in\mathbb Q$, $H$ is an $\eta$-valid solution for the parameters $P'=(\delta,\varepsilon,\eta',K,R)$, with the same $d$, $f$ and $\eta$:
--
--   $$\mathrm{Sol}_{P}(d,f,\eta,H)\ \Longrightarrow\ \mathrm{Sol}_{P'}(d,f,\eta,H).$$
--
--   No assumption is made on $d$, $f$, $\eta$ or the parameters.
--
--   **Role.** In the proof of Theorem 1.4, CompleteSolution produces a $0$-valid solution under parameters whose stored slack is $\delta^2/(100n^2)$, while the robust LMP guarantee (Part I, Theorem D.7) is stated for solutions whose slack is the stored one. This lemma changes the stored slack to $0$, so that the guarantee applies without a slack term.
--
--   **Formalization Note** In the code the parameters are a record with a field $\eta$ that the definition of solutions never reads; conditions 1–4 use only $\delta$, $\varepsilon$, $K$, $R$ and the slack argument.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172). Lean source: `BCFGJPSSV26.FL.sol_eta`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/FL/Run.lean#L298-L302

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_FL_Run

set_option maxSynthPendingDepth 3

@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

theorem sol_eta {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ}
    {H : List (List (Atom m))} (h : Sol P d f η H) (η' : ℚ) : Sol { P with η := η' } d f η H := by sorry

end BCFGJPSSV26.FL
end
