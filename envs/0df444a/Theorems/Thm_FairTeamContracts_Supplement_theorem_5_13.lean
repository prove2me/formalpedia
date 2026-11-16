-- Prove2me | Theorems.Thm_FairTeamContracts_Supplement_theorem_5_13
-- name    : FairTeamContracts.Supplement.theorem_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:11:58.495197+00:00
-- url     : https://prove2.me/theorems/67cb0d2f-890d-4f19-95c7-13f087f6e47a
-- title:
--   Theorem 5.13 — a deterministic value-oracle $(\Gamma-\varepsilon)$-approximation for submodular rewards, $\Gamma\ge0.24988$
-- statement:
--   For every fixed $\varepsilon>0$ there is a deterministic polynomial-time algorithm that uses only value oracles and returns fair revenue at least $(\Gamma-\varepsilon)\,\mathrm{OPT}$, where
--   $$\Gamma:=\max_{t>0}\,(1-e^{-t})\,\widetilde\psi\Bigl(\frac{t^2}{1-e^{-t}}\Bigr)\ge0.24988,$$
--   and, for $C,P\ge0$,
--   $$H(C)=\max_{0\le r\le1}r(1-Cr)=\begin{cases}1-C,&C\le\frac12,\\(4C)^{-1},&C\ge\frac12,\end{cases}\qquad\widetilde\psi(P)=\Bigl(\int_0^1\frac{dz}{H(Pz)}\Bigr)^{-1}.$$
--
--   The statement consists of four claims.
--
--   1. For every $C\ge0$, the maximum of $r(1-Cr)$ over $r\in[0,1]$ equals $1-C$ if $C\le\frac12$ and $(4C)^{-1}$ if $C\ge\frac12$.
--   2. The maximum defining $\Gamma$ is attained at some $t>0$.
--   3. $\Gamma\ge0.24988$.
--   4. For every $\varepsilon>0$ there are a program $p$ and an exponent $k$ such that, for every number $n$ of agents, every monotone normalized submodular success function $f$ and every cost vector $c\ge0$, the run of $p$ on input $c$ with value oracle $f$ halts within $n^k+k$ steps (oracle calls included). Its output is a team $S$ and shares $\alpha$ such that $(S,\alpha)$ is fair and $\mathrm{Rev}(S,\alpha)\ge(\Gamma-\varepsilon)\,\mathrm{OPT}$.
--
--   With $\varepsilon=0.0008$ this gives the advertised $0.249\,\mathrm{OPT}$ guarantee for submodular rewards, where exact optimization is already NP-hard in the additive case (Theorem 5.1).
--
--   **Formalization Note** The machine is the published deterministic value-oracle dialect `OracleProgram` of the real pointer RAM, restricted by `FieldAdmissible`. Its constants are rational; it has $+,-,\times,\div$ and comparisons on reals, pointer increments and comparisons, indirect memory access, and a value instruction returning $f(S)$ for a bitmap $S$ in memory. It has no floor, square root, logarithm or randomness. The program may depend on $\varepsilon$ but not on $n$, $f$ or $c$. Running time counts every executed instruction. $0.24988$ is the exact decimal $24988/100000$.
--
--   Differences from the source:
--   - reading: "deterministic polynomial-time algorithm using only value oracles" (no machine named) → a FieldAdmissible program of the published deterministic value-oracle real pointer RAM (rational constants, field operations, comparisons, pointer operations, value queries; no floor, square root or logarithm), halting within n^k + k steps for every n, f, c; reason: the paper counts value queries and exact real operations (pp.25, 31); this machine is no stronger than a unit-cost real RAM with floor, so the existence claim is not weakened, and the floors the algorithm uses (⌊tK⌋, ⌈1000/ε⌉, J) are a counting loop or constants of the program
--   - encoding: the maxima defining H(C) and Γ → suprema, with their attainment and values stated as conclusions (IsGreatest); reason: the same numbers once the maxima exist, which clauses 1 and 2 assert
--   - encoding: input (value oracle for f, costs) and output (a fair contract and its team) → oracleInput (n in pointer 0, costs in memory cells 0..n−1) and the published output cells outputTeam, outputContract; reason: a fixed layout is needed to state the run
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 5.13, eqs. (17)–(18), p.25 (PDF 26); proof pp.25–32, Appendix E

import Mathlib
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular
import Definitions.Def_FairTeamContracts_IsSuccessFn
import Definitions.Def_FairTeamContracts_IsFair
import Definitions.Def_FairTeamContracts_rev
import Definitions.Def_FairTeamContracts_optFair
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_OracleMachine
import Definitions.Def_FairTeamContracts_Supplement_GammaConst
import Definitions.Def_FairTeamContracts_Supplement_oracleInput

namespace FairTeamContracts.Supplement

open TransparencyTeamContracts.Submodular.Supplement

/-- **Theorem 5.13** (Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript
sha256 b8a12d9b…), Theorem 5.13, eqs. (17)–(18), p.25; proof pp.25–32 and Appendix E): "For
every fixed ε > 0, there exists a deterministic polynomial-time algorithm using only value
oracles, and it returns fair revenue at least (Γ − ε)OPT, such that
Γ := max_{t>0} (1 − e^{−t}) ψ̃(t²/(1 − e^{−t})) ≥ 0.24988, where for C, P ≥ 0,
H(C) = max_{0≤r≤1} r(1 − Cr) = 1 − C for C ≤ 1/2 and (4C)^{−1} for C ≥ 1/2, and
ψ̃(P) = (∫₀¹ dz / H(Pz))^{−1}."

The statement has four clauses.

1. For every `C ≥ 0`, the maximum of `r(1 − C r)` over `r ∈ [0, 1]` exists and equals `1 − C`
   if `C ≤ 1/2` and `1/(4C)` if `C ≥ 1/2`; in particular `H(C)` is that value.
2. The maximum defining `Γ` is attained: `Γ` is the greatest value of
   `(1 − e^{−t}) ψ̃(t²/(1 − e^{−t}))` over `t > 0`.
3. `Γ ≥ 0.24988`.
4. For every `ε > 0` there are a deterministic value-oracle program `p` (rational constants, field
   operations and comparisons only) and an exponent `k` such that for every number of agents
   `n`, every monotone normalized submodular success function `f` and every cost vector `c ≥ 0`,
   the run of `p` on the costs halts within `n^k + k` steps (oracle calls included) with an output
   team `S` and shares `α` forming a fair contract with `Rev(S, α) ≥ (Γ − ε) · OPT`.

**Formalization Note.** The machine is the published deterministic value-oracle dialect
`OracleProgram` of the real pointer RAM, restricted by `FieldAdmissible` (no square root,
logarithm, accept or reject instruction; rational constants). `f` is reachable only through the
value instruction; the input holds `n` (pointer 0) and the costs (`oracleInput`); the output team
and shares are read by `outputTeam`, `outputContract`. `Computes` requires an actual halted run
within the step bound; the query bound is set equal to it. The program may depend on `ε` but not
on `n`, `f` or `c`. `H`, `ψ̃` and `Γ` are `Hfun`, `psiTilde` and `GammaConst` (a supremum, whose
attainment is clause 2). OPT is the published `optFair`. -/
theorem theorem_5_13 :
    (∀ C : ℝ, 0 ≤ C →
      IsGreatest ((fun r : ℝ => r * (1 - C * r)) '' Set.Icc 0 1)
        (if C ≤ 1 / 2 then 1 - C else (4 * C)⁻¹) ∧
      Hfun C = if C ≤ 1 / 2 then 1 - C else (4 * C)⁻¹) ∧
    IsGreatest (gammaObj '' Set.Ioi 0) GammaConst ∧
    (24988 / 100000 : ℝ) ≤ GammaConst ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ (p : OracleProgram) (k : ℕ), FieldAdmissible p ∧
        ∀ (n : ℕ) (f : Finset (Fin n) → ℝ) (c : Fin n → ℝ),
          IsSuccessFn f → SubsamplingSM.Offline.IsSubmodular f → (∀ i, 0 ≤ c i) →
          Computes p f (oracleInput c) (n ^ k + k) (n ^ k + k)
            (fun α S => IsFair f c S α ∧ (GammaConst - ε) * optFair f c ≤ rev f S α) := by sorry

end FairTeamContracts.Supplement
