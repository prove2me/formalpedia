-- Prove2me | Theorems.Thm_BipColorHard_lemma_28
-- name    : BipColorHard.lemma_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:07.2782+00:00
-- url     : https://prove2.me/theorems/68de8b2e-b40e-4ef9-93b3-37c2fd1a5c31
-- title:
--   Lemma 28 (= Lemma 12) — the phases are exactly $(P_S,R_S)$, $(R_S,P_S)$, all nondegenerate
-- statement:
--   Let $q=2k+1\ge3$, $D=q+1$ for $q\ge5$ and $D=5$ for $q=3$, and $p=D/(D-1)$. A phase is a maximizer of $L(P,R)=P^{\mathsf T}BR/(\|P\|_p\|R\|_p)$ with both vectors normalized to coordinate sum one.
--
--   1. For each $S\in\Omega$ there is a unique phase $(P_S,R_S)$ in which both vectors are positive and constant on $S$ and on $S^{\mathrm c}$, with $P_{S,i}>P_{S,j}$ and $R_{S,i}<R_{S,j}$ whenever $i\in S$, $j\in S^{\mathrm c}$.
--   2. The phases are exactly $(P_S,R_S)$ and $(R_S,P_S)$ for $S\in\Omega$.
--   3. At each phase, the Hessian of $L$ is negative definite on $T_0$.
--
--   This is the classification of the dominant phases of bipartite colorings for odd $q$, and the only result of §7 needed elsewhere in the manuscript.
--
--   Differences from the source:
--   - encoding: negative definite Hessian → the restriction of the function to $(P,R)+T_0$ is twice continuously differentiable at $(P,R)$ with negative second derivative in every nonzero direction of $T_0$; reason: the Hessian is a quadratic form on $T_0$ of a function smooth near the pair
--   - encoding: Lemma 12 and its restatement Lemma 28, with "the same statements hold for $q=3$, $D=5$" → one item for every $k\ge1$ with $D$ given by `bipDeg`; reason: the manuscript calls Lemma 28 Lemma 12 restated; $P^{\mathsf T}BR$ equals $1-\sum_iP_iR_i$ on probability vectors and on the lines of $T_0$
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 28, p.31 (PDF p.33); Lemma 12, pp.12–13 (PDF pp.14–15)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_RandomGraph

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 28**, p.31 (PDF p.33) (= Lemma 12, pp.12–13, PDF pp.14–15), manuscript sha256 78a66d1f…, for every
`q = 2k + 1 ≥ 3`, with `D` of §3 and `p = D/(D - 1)`. For each `S ∈ Ω` there is a unique phase `(P_S, R_S)` in which both
vectors are positive and constant on `S` and on `Sᶜ`, with `P_{S,i} > P_{S,j}` and `R_{S,i} < R_{S,j}` whenever `i ∈ S`,
`j ∈ Sᶜ`. The phases are exactly `(P_S, R_S)` and `(R_S, P_S)` for `S ∈ Ω`. At each phase, the Hessian of `L` is negative
definite on `T₀`.

**Formalization Note.** The case `q = 3`, `D = 5` is "the same statements" in the manuscript; `bipDeg` covers both. -/
theorem lemma_28 (k : ℕ) (hk : 1 ≤ k) :
    ∃ Pf Rf : Omega k → Fin (2 * k + 1) → ℝ,
      IsPhaseFamily (expP (bipDeg (2 * k + 1))) Pf Rf ∧
      (∀ P R : Fin (2 * k + 1) → ℝ, IsPhase (expP (bipDeg (2 * k + 1))) P R ↔
        ∃ S : Omega k, (P = Pf S ∧ R = Rf S) ∨ (P = Rf S ∧ R = Pf S)) ∧
      ∀ P R : Fin (2 * k + 1) → ℝ, IsPhase (expP (bipDeg (2 * k + 1))) P R →
        HessNegDefOnT0 (objL (expP (bipDeg (2 * k + 1)))) P R := by sorry

end BipColorHard
