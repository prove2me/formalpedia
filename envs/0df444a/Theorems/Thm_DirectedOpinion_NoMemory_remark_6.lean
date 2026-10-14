-- Prove2me | Theorems.Thm_DirectedOpinion_NoMemory_remark_6
-- name    : DirectedOpinion.NoMemory.remark_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:32.689853+00:00
-- url     : https://prove2.me/theorems/028f16a7-d7c8-483e-ad44-4312d4efd36e
-- title:
--   Remark 6, p. 10 — with c + d = 1, 𝓡* = Σ_j 𝓒_j 𝓡_j + 𝓦_∅^(0), the 𝓡_j i.i.d. endogenous solutions of the SFPE
-- statement:
--   Work in the delayed marked Galton–Watson model of the Setting and assume $c+d=1$ (no memory: the autoregressive term of recursion (1) vanishes). For each $j\ge1$ let
--   $$\mathcal R_j=\sum_{s=1}^{\infty}\sum_{|\mathbf i|=s-1}\frac{\Pi_{(j,\mathbf i)}}{\mathcal C_j}\,\mathcal W^{(s)}_{(j,\mathbf i)},$$
--   display (7), where $\Pi_{(j,\mathbf i)}/\mathcal C_j$ is the product of the weights along the path from $j$ to $(j,\mathbf i)$. Then:
--
--   1. (display (6)) for every outcome,
--   $$\mathcal R^*=\sum_{s=0}^{\infty}\sum_{|\mathbf j|=s}\Pi_{\mathbf j}\mathcal W^{(s)}_{\mathbf j}=\sum_{j=1}^{\mathcal N_\emptyset}\mathcal C_j\mathcal R_j+\mathcal W^{(0)}_\emptyset ;$$
--   2. the $\mathcal R_j$, $j\ge1$, are i.i.d., and the whole family is independent of the root's mark $\boldsymbol{\mathcal X}_\emptyset$ and of the root's uniforms $(U^{(k)}_\emptyset)_{k\ge0}$;
--   3. $\mathcal R:=\mathcal R_1$ solves the branching stochastic fixed-point equation (the smoothing transform) through its own endogenous copies: for every outcome
--   $$\mathcal R_1=\sum_{j=1}^{\mathcal N_1}\mathcal C_{(1,j)}\mathcal R_{(1,j)}+\mathcal W^{(1)}_1,$$
--   where $\mathcal R_{(1,j)}=\sum_{s\ge0}\sum_{|\mathbf i|=s}\frac{\Pi_{(1,j,\mathbf i)}}{\Pi_{(1,j)}}\mathcal W^{(s+2)}_{(1,j,\mathbf i)}$, and the $\mathcal R_{(1,j)}$, $j\ge1$, are i.i.d. with the law of $\mathcal R$ and independent of $(\boldsymbol{\mathcal X}_1,U^{(1)}_1)$, hence of $(\mathcal N_1,\mathcal W^{(1)}_1,\mathcal C_{(1,1)},\mathcal C_{(1,2)},\dots)$.
--
--   In words, without memory the root's opinion is the weighted average of i.i.d. copies of the "special endogenous solution" of the smoothing transform, plus the root's own signal. This is the decomposition on which the proofs of Propositions 4 and 5 rest.
--
--   **Formalization Note.** Children are 0-based: the paper's $\mathcal R_j$ is `Rsub … [j-1] 1` and its $\mathcal R_{(1,j)}$ is `Rsub … [0, j-1] 2`. The paper's convention "$\Pi_{(j,\mathbf i)}/\mathcal C_j\equiv1$ if $\mathcal C_j=0$" is replaced by the relative path weight, which needs no division. Part 2 includes independence from the root's mark and uniforms, which the paper uses in the proof of Propositions 4 and 5 (p. 30, "the $\{\mathcal R_i\}$ are independent of $\boldsymbol{\mathcal X}_\emptyset$"). The SFPE "$\mathcal R\overset{\mathcal D}{=}\sum\mathcal C_{(1,j)}\mathcal R_j+\mathcal W_1^{(1)}$ with i.i.d. copies independent of the coefficients" is stated in its endogenous form: a pathwise identity together with the i.i.d. and independence properties of the copies, which implies the identity in law. The families are indexed by all $j\in\mathbb N$ (also beyond the in-degree); the statements hold for all of them. The series are summable for every outcome since $|\mathcal W|\le1$ and the weights below each node sum to at most $c<1$.
-- source:
--   Fraiman, Lin and Olvera-Cravioto, Opinion dynamics on directed complex networks, arXiv:2209.00969v2, p. 10, Remark 6, displays (6)–(7); p. 30, proof of Propositions 4 and 5

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

namespace DirectedOpinion.NoMemory

/-- Remark 6, p. 10 (no memory, c + d = 1, delayed marked Galton–Watson tree).
(a) (6): 𝓡* = Σ_{s≥0} Σ_{|j|=s} Π_j 𝓦_j^(s) = Σ_{j=1}^{𝓝_∅} 𝓒_j 𝓡_j + 𝓦_∅^(0), pathwise, where
`Rsub … [] 0` is the middle series and 𝓡_j of (7) is `Rsub … [j] 1` (0-based `j`).
(b) The 𝓡_j are i.i.d., and independent of the root's mark and of the root's uniforms.
(c) 𝓡 := 𝓡_1 solves the SFPE 𝓡 = Σ_{j=1}^{𝓝_1} 𝓒_(1,j) 𝓡_(1,j) + 𝓦_1^(1) pathwise, with the
𝓡_(1,j) := `Rsub … [0, j] 2` i.i.d. copies of 𝓡, independent of (𝓧_1, U_1^(1)). -/
theorem remark_6 {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : MarkFns M) (X : Label → Ω → M)
    (U : Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1) :
    -- (a) equation (6)
    (∀ ω, Rstar mk X U ζ c d ω = Rsub mk X U ζ c d [] 0 ω ∧
      Rsub mk X U ζ c d [] 0 ω =
        ∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j * Rsub mk X U ζ c d [j] 1 ω +
          W mk X U ζ c d [] 0 ω) ∧
    -- (b) the 𝓡_j are i.i.d. and independent of the root
    iIndepFun (fun (j : ℕ) ω => Rsub mk X U ζ c d [j] 1 ω) P ∧
    (∀ j : ℕ, IdentDistrib (Rsub mk X U ζ c d [j] 1) (Rsub mk X U ζ c d [0] 1) P P) ∧
    IndepFun (fun ω (j : ℕ) => Rsub mk X U ζ c d [j] 1 ω)
      (fun ω => (X [] ω, fun k : ℕ => U [] k ω)) P ∧
    -- (c) the branching SFPE with i.i.d. endogenous copies
    (∀ ω, Rsub mk X U ζ c d [0] 1 ω =
      ∑ j ∈ Finset.range (mk.N (X [0] ω)), mk.C (X [0] ω) j * Rsub mk X U ζ c d [0, j] 2 ω +
        W mk X U ζ c d [0] 1 ω) ∧
    iIndepFun (fun (j : ℕ) ω => Rsub mk X U ζ c d [0, j] 2 ω) P ∧
    (∀ j : ℕ, IdentDistrib (Rsub mk X U ζ c d [0, j] 2) (Rsub mk X U ζ c d [0] 1) P P) ∧
    IndepFun (fun ω (j : ℕ) => Rsub mk X U ζ c d [0, j] 2 ω)
      (fun ω => (X [0] ω, U [0] 1 ω)) P := by sorry

end DirectedOpinion.NoMemory
