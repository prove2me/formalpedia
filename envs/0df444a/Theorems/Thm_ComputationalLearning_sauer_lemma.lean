-- Prove2me | Theorems.Thm_ComputationalLearning_sauer_lemma
-- name    : ComputationalLearning.sauer_lemma
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:12:53.122007+00:00
-- url     : https://prove2.me/theorems/ea286dc0-0683-4b35-aac4-151b46169f07
-- title:
--   Lemma 3.1 (Sauer): if VCD(C) ≤ d then Π_C(m) ≤ Φ_d(m) for every m
-- statement:
--   **Lemma 3.1.** If $\mathrm{VCD}(C) = d$, then for any $m$, $\Pi_C(m) \le \Phi_d(m)$.
--
--   Formally: for every concept class $C$ with $\mathrm{vcDim}(C) \le d$ and every $m$, $\Pi_C(m) \le \Phi_d(m)$, where $\Pi_C(m)$ is the maximum number of dichotomies realized on a set of $m$ points and $\Phi_d$ is defined by the recurrence of Definition 11.
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §3.4 pp. 55-56, Lemma 3.1 with its proof (induction on d and m through the class C')

import Definitions.Def_ComputationalLearning_VC

open MeasureTheory

namespace ComputationalLearning

/-- **Lemma 3.1** (p. 55, Sauer's lemma). If `VCD(C) = d`, then for any `m`, `Π_C(m) ≤ Φ_d(m)`.
Stated for every class of VC dimension at most `d`. -/
theorem sauer_lemma {X : Type*} [MeasurableSpace X] (C : Set (X → Bool)) (d : ℕ)
    (hd : vcDim C ≤ d) (m : ℕ) :
    growth C m ≤ Phi d m := by sorry

end ComputationalLearning
