-- Prove2me | Theorems.Thm_DisclosureDiscretion_InfoSystem_equilibrium_exists
-- name    : DisclosureDiscretion.InfoSystem.equilibrium_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:37.710487+00:00
-- url     : https://prove2.me/theorems/aeef5b1f-3a78-41af-a88a-786433e70f09
-- title:
--   §3.1, p. 22 (PDF 24) — the D-subgame has an equilibrium for every admissible k
-- statement:
--   Assume the standing assumptions $0<t<1$, $k>0$, $0<p<1$, $\bar c>k/[t(1-t)]$. Then the $D$-subgame has an equilibrium: there are a value of silence $x$ and a union mixing probability $q$ such that
--   $$q\in[0,1],\quad x>\tfrac kt\Rightarrow q=1,\quad x<\tfrac kt\Rightarrow q=0,$$
--   and $x$ is the conditional expectation of $c$ given silence, computed from the informed CEO's best-response nondisclosure set at the silence price $[q(1-t)+1-q]x$.
--
--   This is the content of the paper's remark that the cases of Propositions 1 through 4 encompass all $k$-values.
--
--   **Formalization Note** The remark also says that these cases "fully characterize" the CEO's discretion; that uniqueness claim is not formalized, because the $D$-subgame has several equilibria just below $k_{2A}$ (e.g. $\bar c=1$, $t=0.4$, $p=0.8$, $k=k_{2A}-0.001$). No hypothesis on $k_{2B}$ is needed here.
-- source:
--   Arya & Ramanan, Endogenizing discretion in disclosures, authors' manuscript (SSRN 3935991, June 2022), p. 22 (PDF 24), §3.1, closing remark after Proposition 4

import Mathlib
import Definitions.Def_DisclosureDiscretion_InfoSystem_Model

namespace DisclosureDiscretion.InfoSystem

theorem equilibrium_exists (cbar t p k : ℝ) (h : Standing cbar t p k) :
    ∃ x q : ℝ, IsDEquilibrium cbar t p k x q := by sorry

end DisclosureDiscretion.InfoSystem
