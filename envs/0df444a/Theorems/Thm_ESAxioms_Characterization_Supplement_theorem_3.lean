-- Prove2me | Theorems.Thm_ESAxioms_Characterization_Supplement_theorem_3
-- name    : ESAxioms.Characterization.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:33:11.360806+00:00
-- url     : https://prove2.me/theorems/27d072d0-869b-462f-822d-ff376af941a3
-- title:
--   Theorem 3, p. 12 — five equivalent forms of p-concentration: with S, pairs (Xᵢ, S − Xᵢ), increasing transforms, a copula with C(p, …, p) = p
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and $(X_1,\dots,X_n)$, $n\ge1$, a random vector with $S=X_1+\dots+X_n$. A vector is *$p$-concentrated* if its components share a common $p$-tail event, an event $A$ with $\mathbb P(A)=1-p$ on which each component almost surely dominates its values on $A^c$.
--
--   **Theorem 3.** The following statements are equivalent:
--   1. $(X_1,\dots,X_n)$ is $p$-concentrated;
--   2. $(X_1,\dots,X_n,S)$ is $p$-concentrated;
--   3. $(X_i,S-X_i)$ is $p$-concentrated for every $i=1,\dots,n$;
--   4. $(f_1(X_1),\dots,f_n(X_n))$ is $p$-concentrated for all increasing functions $f_1,\dots,f_n:\mathbb R\to\mathbb R$;
--   5. there is a copula $C$ of $(X_1,\dots,X_n)$ with
--   $$C(p,\dots,p)=p .$$
--
--   The theorem is an analogue for $p$-concentration of Denneberg's characterization of comonotonicity. Statement 3 gives $p$-concentration of the whole vector from $p$-concentration of $n$ pairs without any continuity assumption, and statement 5 requires the diagonal value $p$ only for *some* copula, which matters when the marginals have atoms (Remark 4). Theorem 3 is used for Theorem 4 and for the VaR inequalities of Theorem 6.
--
--   **Formalization Note** Components are measurable functions $\Omega\to\mathbb R$; increasing means `Monotone`. A copula is the published `ProbabilityTheory.Copula n` with distribution function `Copula.cdf`, and "$C$ is a copula of $(X_1,\dots,X_n)$" is the Sklar identity $\mathbb P(X_1\le x_1,\dots,X_n\le x_n)=C(F_{X_1}(x_1),\dots,F_{X_n}(x_n))$ for all $x\in\mathbb R^n$ (definition item of this mission). No continuity of the marginal distributions is assumed.
--
--   Differences from the source:
--   - encoding: standing assumption of §1.2, p. 5: the probability space is atomless → explicit hypothesis hP : IsAtomless P; reason: the paper fixes an atomless space once for the whole paper; Lean has no standing assumptions
--   - encoding: random variables X : Ω → ℝ → functions Ω → ℝ with an explicit Measurable hypothesis; reason: Lean convention; the base mission represents random variables as functions, not a.e. classes
--   - reading: any random vector (X₁, …, Xₙ) → explicit hypothesis 0 < n; reason: a random vector has at least one component; at n = 0 the only copula has C() = 1 ≠ p, so (v) would fail while (i)–(iv) hold vacuously
--   - encoding: a copula C of (X₁, …, Xₙ) (Nelsen 2006) and the value C(p, …, p) → C : ProbabilityTheory.Copula n with IsCopulaOf P Xs C (Sklar identity for every x ∈ ℝⁿ) and C.cdf (fun _ => projIcc 0 1 p) = p; reason: the published copula is a probability measure on [0, 1]ⁿ with uniform marginals; projIcc is the identity on [0, 1] and only types p
--   - encoding: (X₁, …, Xₙ, S) and (Xᵢ, S − Xᵢ) → Fin.snoc Xs S and ![Xs i, S - Xs i] with S = fun ω => ∑ i, Xs i ω; reason: Lean vector notation; same vectors
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 12, Theorem 3 (proof pp. 30–31); Remark 4, p. 13; Definition 2, p. 12

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Supplement_Setting

open MeasureTheory ProbabilityTheory

namespace ESAxioms.Characterization.Supplement

theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) (Xs : Fin n → Ω → ℝ) (hXs : ∀ i, Measurable (Xs i)) :
    let S : Ω → ℝ := fun ω => ∑ i, Xs i ω
    List.TFAE [
      IsPConcentrated P p Xs,
      IsPConcentrated P p (Fin.snoc (α := fun _ => Ω → ℝ) Xs S),
      ∀ i, IsPConcentrated P p ![Xs i, S - Xs i],
      ∀ f : Fin n → ℝ → ℝ, (∀ i, Monotone (f i)) →
        IsPConcentrated P p (fun i ω => f i (Xs i ω)),
      ∃ C : ProbabilityTheory.Copula n, IsCopulaOf P Xs C ∧
        C.cdf (fun _ => Set.projIcc (0 : ℝ) 1 zero_le_one p) = p] := by sorry

end ESAxioms.Characterization.Supplement
