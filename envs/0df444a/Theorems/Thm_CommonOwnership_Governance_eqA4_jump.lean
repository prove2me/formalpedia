-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eqA4_jump
-- name    : CommonOwnership.Governance.eqA4_jump
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:03.208983+00:00
-- url     : https://prove2.me/theorems/3f4e50a5-3e7f-41b4-a2e2-a2313da1ee23
-- title:
--   (A4)–(A5), p. 39 (PDF p. 42) — S(s⁺) − S(0) = (ξ²/(2γ)) K Π*₊
-- statement:
--   Let $\xi>0$ and $\gamma>0$. With the quadratic cost and the monitoring rule (21), let $S(s)=\nu^*(s)\Pi^*(s)$ be the joint surplus along an industry-profit path $\Pi^*$. Let $s^+$ be a stake with $\Pi^*_+=\Pi^*(s^+)\neq0$ and write $\Pi^*_0=\Pi^*(0)$. Then
--   $$\Delta S\equiv S(s^+)-S(0)=\frac{\xi^2}{2\gamma}\,K\,\Pi^*_+,\qquad K=\Big[2\gamma\beta\frac{1-\xi}{\xi^2}+\beta^2\Big]\frac{\Pi^*_+-\Pi^*_0}{\Pi^*_+}-s^{+2}.$$
--
--   The proof of Proposition 3 uses this identity at a switching point, where the equilibrium jumps between $s^*=0$ and an interior $s^+$ and $\Delta S=0$; the sign of $\Delta S$ is that of $K$.
--
--   **Formalization Note** The paper prints the constant as $\xi^2/\gamma$. With $K$ exactly as printed in (A5) the identity holds with $\xi^2/(2\gamma)$ (check: $\beta=4/5$, $\xi=1/2$, $\gamma=2$, $s^+=2/5$ with the Cournot profits of Appendix B, Example 1, gives $\Delta S=173/72670=(\xi^2/(2\gamma))K\Pi^*_+$). The paper uses only the sign, so its argument is unaffected. The identity is stated for every $s^+$, not only at a switching point.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), Appendix A, proof of Proposition 3, p. 39 (PDF p. 42), (A4), (A5)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- (A4)–(A5), p. 39: under (20)–(21), `S(s⁺) − S(0) = (ξ²/(2γ)) K Π*₊` with `K` of (A5). The
printed constant is `ξ²/γ`; with `K` as printed in (A5) the identity holds with `ξ²/(2γ)`. -/
theorem eqA4_jump (β ξ γ sp : ℝ) (hξ : 0 < ξ) (hγ : 0 < γ) (Pi_ : ℝ → ℝ) (hPi : Pi_ sp ≠ 0) :
    surplusQ β ξ γ Pi_ sp - surplusQ β ξ γ Pi_ 0 =
      ξ ^ 2 / (2 * γ) * Kfun β ξ γ sp (Pi_ 0) (Pi_ sp) * Pi_ sp := by sorry

end CommonOwnership.Governance
