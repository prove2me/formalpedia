-- Prove2me | Theorems.Thm_APSCounting893_Main_nested_trailing_specialization
-- name    : APSCounting893.Main.nested_trailing_specialization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:26:02.881515+00:00
-- url     : https://prove2.me/theorems/b282b88b-84d0-4041-92b3-6d40d634daf8
-- title:
--   Lemma 6.2 — Stability of nested trailing coefficients
-- statement:
--   Let $R(\Theta,t_1,\ldots,t_k,T)$ be a nonzero rational polynomial of total degree at most $D$, for arbitrary $k$. There exist nonzero rational polynomials $A_1(\Theta),\ldots,A_k(\Theta)$, each of degree at most $D$, such that every specialization with $A_i(\theta)\ne0$ satisfies
--
--   $$(\mathrm{TC}_{t_k}\cdots\mathrm{TC}_{t_1}R)(\theta,T)=\mathrm{TC}_{t_k}\cdots\mathrm{TC}_{t_1}(R(\theta,t_1,\ldots,t_k,T)).$$
--
--   The exceptional polynomials are chosen before the parameter values. Specialization is allowed in every field extension of $\mathbb Q$, including $\mathbb C$; no nonvanishing of the desired trailing coefficient is assumed separately.
--
--   Differences from the source:
--   - generalization: parameter specialization in the rational-polynomial setting → specialization in any field equipped with a rational algebra structure; reason: the coefficient argument is unchanged under the injective rational field map and includes every rational or complex source specialization
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 6.2, p. 24, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_CoefficientLanguages

set_option autoImplicit false

namespace APSCounting893.Main

theorem nested_trailing_specialization (s k D : ℕ) (R : MvPolynomial (Fin (s + (k + 1))) ℚ)
    (hR : R ≠ 0) (hdegree : R.totalDegree ≤ D) :
    ∃ A : Fin k → MvPolynomial (Fin s) ℚ,
      (∀ i, A i ≠ 0 ∧ (A i).totalDegree ≤ D) ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (theta : Fin s → K),
        (∀ i, MvPolynomial.eval₂ (algebraMap ℚ K) theta (A i) ≠ 0) →
        specializeParameters theta
          (nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc.natAdd s)) R) =
          nestedTrailing (List.ofFn (fun i : Fin k => i.castSucc)) (specializeParameters theta R) := by sorry

end APSCounting893.Main
