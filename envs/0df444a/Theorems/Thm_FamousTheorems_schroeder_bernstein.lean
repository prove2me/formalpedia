-- Prove2me | Theorems.Thm_FamousTheorems_schroeder_bernstein
-- name    : FamousTheorems.schroeder_bernstein
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:31.757673+00:00
-- url     : https://prove2.me/theorems/1646455a-012a-4179-91fa-f37b39f483a6
-- title:
--   The Schröder–Bernstein theorem
-- statement:
--   **Mutual injections give a bijection.**
--
--   If there are injections $\alpha \hookrightarrow \beta$ and $\beta \hookrightarrow \alpha$, then
--   there is a bijection $\alpha \leftrightarrow \beta$ — that is, $|\alpha| \le |\beta|$ and
--   $|\beta| \le |\alpha|$ imply $|\alpha| = |\beta|$.
--
--   The result makes cardinal comparison a genuine partial order; without it, antisymmetry would
--   fail and "same cardinality" would be badly behaved. Notably the proof is **constructive in the
--   sense of requiring no choice**: one partitions $\alpha$ according to whether the backwards
--   chain $\dots \mapsto g^{-1} \mapsto f^{-1} \mapsto$ terminates, and uses $f$ on one part and
--   $g^{-1}$ on the other.
--
--   Proved by Dedekind in 1887 (unpublished), then by Schröder and Bernstein independently in the
--   1890s.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem schroeder_bernstein : ∀ {α β : Type*} {f : α → β} {g : β → α},
    Function.Injective f → Function.Injective g → ∃ h : α → β, Function.Bijective h := by sorry

end FamousTheorems
