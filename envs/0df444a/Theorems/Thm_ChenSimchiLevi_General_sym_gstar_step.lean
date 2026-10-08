-- Prove2me | Theorems.Thm_ChenSimchiLevi_General_sym_gstar_step
-- name    : ChenSimchiLevi.General.sym_gstar_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:11:39.415483+00:00
-- url     : https://prove2.me/theorems/7858b1ed-6d41-4e85-9337-ceb264da2cfa
-- title:
--   Symmetric concavity of optimized current profit
-- statement:
--   Fix a period $t$ satisfying the paper's model assumptions and a continuous continuation value $V$ that is symmetrically $k$-concave with polynomial growth. If the associated one-period profit $g_t^V(y,d)$ is jointly continuous, then its best-demand value is symmetrically $k$-concave:
--   $$y\longmapsto \max_{d\in[\underline d_t,\overline d_t]}g_t^V(y,d)\quad\text{is symmetrically $k$-concave}.$$
--   This is the induction step used for the first assertion of Theorem 4.1(c).
--
--   **Formalization Note** The function is represented by the supremum over the admissible demand interval; continuity and compactness ensure it is attained.
-- source:
--   Chen, Simchi-Levi, Operations Research 52(6) (2004), p. 892, §4, proof of Theorem 4.1, symmetric versions of equations (6)–(7)

import Definitions.Def_ChenSimchiLevi_General_Model
import Definitions.Def_ChenSimchiLevi_General_SymKConvex

set_option autoImplicit false

namespace ChenSimchiLevi.General

/-- The symmetric version of (6)–(7), proof of Theorem 4.1, p. 892. -/
theorem sym_gstar_step (M : Model) (hA : M.Assumptions)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 M.T) (V : ℝ → ℝ)
    (hVcont : Continuous V) (hVsym : SymKConvex M.k (fun x => -V x))
    (hVgrowth : ∃ C : ℝ, ∀ x, |V x| ≤ C * (1 + |x| ^ M.ρ))
    (hgcont : ContinuousOn (fun q : ℝ × ℝ => M.gWith V t q.1 q.2)
      (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t))) :
    SymKConvex M.k (fun y => -M.GstarWith V t y) := by sorry

end ChenSimchiLevi.General
