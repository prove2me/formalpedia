-- Prove2me | Theorems.Thm_ElectroweakWiki_neutral_rotation_inverse
-- name    : ElectroweakWiki.neutral_rotation_inverse
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T20:04:21.929641+00:00
-- url     : https://prove2.me/theorems/94a53256-6118-484b-aa9a-fa65755cf23f
-- title:
--   $(\gamma, Z^0)$ is a rotation of $(B, W_3)$
-- statement:
--   For every angle $\theta$ and real field values $B, W_3$, put
--
--   $$\begin{pmatrix}\gamma\\ Z^0\end{pmatrix} = \begin{pmatrix}\cos\theta & \sin\theta\\ -\sin\theta & \cos\theta\end{pmatrix}\begin{pmatrix}B\\ W_3\end{pmatrix}.$$
--
--   Then the transformation is inverted by the transposed matrix, $B = \cos\theta\,\gamma - \sin\theta\, Z^0$ and $W_3 = \sin\theta\,\gamma + \cos\theta\,Z^0$, and it preserves the sum of squares: $\gamma^2 + (Z^0)^2 = B^2 + W_3^2$.
--
--   This is the precise content of the article's remark that "the axes representing the particles have essentially just been rotated, in the $(W_3, B)$ plane, by the angle $\theta_W$".
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; Section Formulation, matrix equation for (γ, Z0) and the sentence 'The axes representing the particles have essentially just been rotated, in the (W3, B) plane, by the angle θw' (p. 3 of the PDF)

import Definitions.Def_ElectroweakWiki_defs
open Matrix

namespace ElectroweakWiki

theorem neutral_rotation_inverse (θ B W3 : ℝ) :
    B = Real.cos θ * photonField θ B W3 - Real.sin θ * zField θ B W3 ∧
      W3 = Real.sin θ * photonField θ B W3 + Real.cos θ * zField θ B W3 ∧
      photonField θ B W3 ^ 2 + zField θ B W3 ^ 2 = B ^ 2 + W3 ^ 2 := by sorry

end ElectroweakWiki
