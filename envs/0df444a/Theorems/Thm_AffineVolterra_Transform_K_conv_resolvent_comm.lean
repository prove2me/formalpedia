-- Prove2me | Theorems.Thm_AffineVolterra_Transform_K_conv_resolvent_comm
-- name    : AffineVolterra.Transform.K_conv_resolvent_comm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:46.374993+00:00
-- url     : https://prove2.me/theorems/214068be-4083-4603-85f3-31e7ef6310cb
-- title:
--   Proof of Lemma 4.4 — commutation of the two resolvents
-- statement:
--   Let $K$ be a locally integrable matrix kernel and $B$ a fixed matrix. Let $R_B$ and $\widetilde R_B$ be the second-kind resolvents of $-KB$ and $-BK$, respectively. Then
--
--   $$
--   K*\widetilde R_B=R_B*K
--   $$
--
--   almost everywhere on positive time. This identity is the deterministic step that permits the two Riccati–Volterra representations to be compared.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, proof of Lemma 4.4, p. 20, first sentence

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Core

open MeasureTheory

namespace AffineVolterra.Transform

/-- The commutation identity used in the proof of Lemma 4.4, p. 20. -/
theorem K_conv_resolvent_comm {d : ℕ} (K : RKernel d)
    (B : Matrix (Fin d) (Fin d) ℝ) (R_B Rtilde_B : RKernel d)
    (hd : 0 < d)
    (hK : KernelLpLoc 1 K)
    (hR : IsResolvent (fun t => -kernelRight K B t) R_B)
    (hRt : IsResolvent (fun t => -kernelLeft B K t) Rtilde_B) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      kernelConv K Rtilde_B t = kernelConv R_B K t := by sorry

end AffineVolterra.Transform
