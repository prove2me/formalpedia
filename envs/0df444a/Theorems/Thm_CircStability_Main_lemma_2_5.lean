-- Prove2me | Theorems.Thm_CircStability_Main_lemma_2_5
-- name    : CircStability.Main.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:39.083225+00:00
-- url     : https://prove2.me/theorems/3b7b790e-a5fc-4232-9b2d-948c14c0a2bd
-- title:
--   Lemma 2.5 — clique number of G[C] ≤ |C| − (d−1)(t−1) (− q for a maximum strong attachment)
-- statement:
--   Let $G$ be a 2-connected graph, $C$ a locally maximal cycle of $G$, and $R$ a component of $G-C$. Let $T$ be a strong attachment of $R$ to $C$, $t=|T|$, $q=|N_C(R)\setminus T|$, and let $\omega$ be the clique number of $G[C]$. Suppose that for any two distinct $x,x'\in T$ the longest $(x,R,x')$-path has length at least $d$, where $d\ge2$. Then:
--   1. $\omega\le|C|-(d-1)(t-1)$;
--   2. if $T$ is a maximum strong attachment, then
--   $$
--   \omega\le|C|-(d-1)(t-1)-q .
--   $$
--
--   Lemma 2.5 converts long detours through a component of $G-C$ into an upper bound on the largest clique on the cycle. It is used in the proofs of Lemmas 4.3 and 4.4.
--
--   **Formalization Note.** Both inequalities are stated in $\mathbb Z$. For $T=\emptyset$ the factor $t-1$ is $-1$, and a natural-number reading would turn the bound into a false one. "The longest $(x,R,x')$-path has length at least $d$" is stated as the existence of an $(x,R,x')$-path of length at least $d$, for distinct $x,x'\in T$.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, pp. 7–8, Lemma 2.5

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
import Definitions.Def_CircStability_Main_Attachment
open Finset SimpleGraph

namespace CircStability.Main

theorem lemma_2_5 (n c d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) {u : Fin n} (C : G.Walk u u) (hC : IsLocallyMaximal G C)
    (hlen : C.length = c) (R : Finset (Fin n)) (hR : CircStability.Bondy.IsComponentOff G C.support.toFinset R)
    (T : Finset (Fin n)) (hT : IsStrongAttachment G C R T) (hd : 2 ≤ d)
    (hpath : ∀ x ∈ T, ∀ x' ∈ T, x ≠ x' →
      ∃ p : G.Walk x x', IsThroughPath R p ∧ d ≤ p.length) :
    ((G.induce ((C.support.toFinset : Finset (Fin n)) : Set (Fin n))).cliqueNum : ℤ) ≤
        (c : ℤ) - ((d : ℤ) - 1) * ((#T : ℤ) - 1) ∧
      (IsMaxStrongAttachment G C R T →
        ((G.induce ((C.support.toFinset : Finset (Fin n)) : Set (Fin n))).cliqueNum : ℤ) ≤
          (c : ℤ) - ((d : ℤ) - 1) * ((#T : ℤ) - 1) -
            (#(attachSet G C.support.toFinset R \ T) : ℤ)) := by sorry

end CircStability.Main
